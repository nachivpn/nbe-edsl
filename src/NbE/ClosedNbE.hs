{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
module NbE.ClosedNbE where

import GExp
import Control.Monad (ap)
import Control.Monad.Identity
import Control.Monad.Except
import Control.Monad.State.Lazy
import Data.Array ( (!), listArray )

class Reifiable a where
  type Sem a :: *
  reify :: Sem a -> Nf a

type Exp  a = GExp Reifiable a
type Prim a = GPrim Reifiable a

-- Normal forms of closed expressions (no neutrals needed!)
data Nf a where
  NLift     :: PrimTy a
    => a -> Nf a
  NUnit     :: ()
    => Nf ()
  NLam      :: (Reifiable a, Reifiable b)
    => (Exp a -> Nf b) -> Nf (a -> b)
  NPair     :: (Reifiable a, Reifiable b)
    => Nf a -> Nf b -> Nf (a,b)
  NInl      :: (Reifiable a)
    => Nf a -> Nf (Either a b)
  NInr      :: (Reifiable b)
    => Nf b -> Nf (Either a b)
  NRetErr   :: (Reifiable a)
    => Nf a -> Nf (Err a)
  NThrow    :: (Reifiable a)
    => String -> Nf (Err a)
  NGetPut   :: (Reifiable a, Reifiable s)
    => (Exp s -> (Nf a, Nf s)) -> Nf (State s a)
  NArr      :: (Reifiable a)
    => Int -> (Exp Int -> Nf a)  -> Nf (Arr a)

embNf :: Nf a -> Exp a
embNf (NLift x)   = Lift x
embNf NUnit       = Unit
embNf (NLam f)    = Lam (\e -> embNf (f e))
embNf (NPair m n) = Pair (embNf m) (embNf n)
embNf (NInl n)    = Inl (embNf n)
embNf (NInr n)    = Inr (embNf n)
embNf (NRetErr n) = RetErr (embNf n)
embNf (NThrow s)  = Throw (Lift s)
embNf (NGetPut f) = Get (Lam $ (\(a,s) -> Put (embNf s) `seqSt` RetSt (embNf a)) . f)
embNf (NArr k f)  = Arr (Lift k) (Lam $ embNf . f)

quote :: Reifiable a => Sem a -> Exp a
quote = embNf . reify

instance Reifiable Int where
  type Sem Int = Int
  reify n      = NLift n

instance Reifiable String where
  type Sem String = String
  reify s         = NLift s

instance Reifiable () where
  type Sem () = ()
  reify ()    = NUnit

instance  (Reifiable a, Reifiable b) => Reifiable (a,b) where
  type Sem (a,b) = (Sem a, Sem b)
  reify (x,y)    = NPair (reify x) (reify y)

instance  (Reifiable a, Reifiable b) => Reifiable (a -> b) where
  type Sem (a -> b) = Sem a -> Sem b
  reify f           = NLam (\ e -> reify (f (eval e)))

instance  (Reifiable a, Reifiable b) => Reifiable (Either a b) where
  type Sem (Either a b) = Either (Sem a) (Sem b)
  reify (Left x)        = NInl (reify x)
  reify (Right x)       = NInr (reify x)

instance  (Reifiable a) => Reifiable (Err a) where
  type Sem (Err a) = Err (Sem a)
  reify            = go . runExcept
    where
    go (Left x)  = NThrow x
    go (Right x) = NRetErr (reify x)

instance  (Reifiable s, Reifiable a) => Reifiable (State s a) where
  type Sem (State s a) = State (Sem s) (Sem a)
  reify m              = NGetPut $ go . runState m . eval
    where
    go (x,y) = (reify x, reify y)

instance  (Reifiable a) => Reifiable (Arr a) where
  type Sem (Arr a) = Arr (Sem a)
  reify arr        = NArr (length narr) ((!) narr . eval)
    where narr :: Arr (Nf a) = fmap reify arr

-- insert values of primitives types in the semantics
drown :: forall a . PrimTy a => a -> Sem a
drown = go (pTypeRep @a)
  where
    go :: forall a . PTypeRep a -> a -> Sem a
    go PTInt    x = x
    go PTString x = x

-- evaluate primitive operations
evalPrim :: Prim a -> Sem a
evalPrim (Mul e1 e2) = eval e1 * eval e2
evalPrim (Add e1 e2) = eval e1 + eval e2
evalPrim (Rec e f x) = rec' (eval e) (eval f) (eval x)
  where
    rec' :: Int -> (Int -> a -> a) -> a -> a
    rec' 0 f x = x
    rec' n f x = rec' (n - 1) f (f n x)

-- evaluate closed expressions
eval :: Exp a -> Sem a
eval (Var x)        = error "Expected expression without unknowns!"
eval Unit           = ()
eval (Lift x)       = drown x
eval (Prim p)       = evalPrim p
eval (Lam f)        = \ x -> eval (f (quote x))
eval (App f e)      = (eval f) (eval e)
eval (Pair e e')    = (eval e , eval e')
eval (Fst e)        = fst (eval e)
eval (Snd e)        = snd (eval e)
eval (Inl e)        = Left (eval e)
eval (Inr e)        = Right (eval e)
eval (Case s f g)   = either (eval f) (eval g) (eval s)
eval (RetErr e)     = return (eval e)
eval (BindErr e e') = eval e >>=  eval e'
eval (Throw e)      = throwError (eval e)
eval (Catch e e')   = catchError (eval e) (eval e')
eval (Get e)        = get >>= eval e
eval (Put e)        = put (eval e)
eval (RetSt e)      = return (eval e)
eval (BindSt e e')  = eval e >>=  eval e'
eval (Arr e e')     = let n = eval e - 1
                      in listArray (0,n) $ [ eval e' i | i <- [0.. n]]
eval (ArrLen e)     = length (eval e)
eval (ArrIx e e')   = eval e ! eval e'
eval (Let e e')     = (eval e') (eval e)
eval (Save e)       = eval e

norm :: Reifiable a => Exp a -> Nf a
norm = reify . eval

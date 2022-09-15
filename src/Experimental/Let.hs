{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Experimental.Let where

import GExp
import Control.Monad (ap, join)
import Control.Monad.State.Lazy ( join, ap, State )

import Arr (mapArr, foldArr)

type Exp  a = GExp Reifiable a
type Prim a = GPrim Reifiable a

instance Semigroup (Exp Int) where
  e1 <> e2 = Prim (Add e1 e2)

instance Monoid (Exp Int) where
  mempty = Lift 0

---------------
-- Normal forms
---------------

-- neutrals
data Ne a where
  NVar    :: (Reifiable a)
    => String -> Ne a
  NApp    :: (Reifiable a)
    => Ne (a -> b) -> Nf a -> Ne b
  NFst    :: (Reifiable b)
    => Ne (a , b)  -> Ne a
  NSnd    :: (Reifiable a)
    => Ne (a , b)  -> Ne b
  NLet    :: (Reifiable a, Reifiable b)
    => Nf a -> Nf (a -> b) -> Ne b

-- normal forms, or "values" and "stuck terms (of positive types)"
data Nf a where
  NUp   :: ()
    => Ne a -> Nf a
  NLift :: (PrimTy a)
    => a -> Nf a
  NInt  :: ()
    => Int -> [Ne Int] -> Nf Int
  NLam  :: (Reifiable a, Reifiable b)
    => (Exp a -> Nf b) -> Nf (a -> b)

-- embed neutrals back into expressions
embNe :: Ne a -> Exp a
embNe (NVar x)   = Var x
embNe (NApp m n) = App (embNe m) (embNf n)
embNe (NLet n m) = Let (embNf n) (embNf m)

-- embed normal forms back into expressions
embNf :: Nf a -> Exp a
embNf (NUp n)     = embNe n
embNf (NLift x)   = Lift x
embNf (NLam f)    = Lam (embNf . f)
embNf (NInt k []) = Lift k
embNf (NInt 0 ns) = foldr1 (\e1 e2 -> Prim (Add e1 e2)) (map embNe ns)
embNf (NInt k ns) = foldr (\n e -> Prim (Add (embNe n) e)) (Lift k) ns

----------------------------
-- Semantics and Reification
----------------------------

class Reifiable a where
  type Sem a :: *
  -- | type-rep for induction on values in semantics
  rTypeRep :: RTypeRep Reifiable a
  -- | "reify" values in semantics to normal forms
  reify    :: Sem a -> Nf a
  -- | "reflect" neutrals to semantics
  reflect  :: Ne a -> Sem a

-- "quote" semantics back to expressions
quote :: Reifiable a => Sem a -> Exp a
quote = embNf . reify

instance Reifiable Int where
  type Sem Int = (Int,[Ne Int])
  rTypeRep        = RTInt
  reify   (k,ns)  = NInt k ns
  reflect n       = (0,[n])

instance  (Reifiable a, Reifiable b) => Reifiable (a -> b) where
  type Sem (a -> b) = (Sem a -> Sem b, Nf (a -> b))
  rTypeRep          = RTFun rTypeRep rTypeRep
  reify             = snd
  reflect n         = (\ y -> (reflect (NApp n (reify y))), NUp n)

-------------
-- Evaluation
-------------

-- insert primitive values into semantics
drown :: forall a . PrimTy a => a -> Sem a
drown = go (pTypeRep @a)
  where
    go :: forall a . PTypeRep a -> a -> Sem a
    go PTInt x = (x,[])

-- evaluate primitives operators
evalPrim :: forall a . Reifiable a
  => Prim a -> Sem a
evalPrim (Add e1 e2) =
    let (k1,ns1) = eval e1
        (k2,ns2) = eval e2
    in (k1 + k2, ns1 ++ ns2)

-- evaluate expressions
eval :: forall a . Reifiable a
  => Exp a -> Sem a
eval (Var s)       = reflect @a (NVar s)
eval (Lift x)      = drown x
eval (Prim e)      = evalPrim e
eval (Lam f)       = (eval . f . quote , NLam (reify . eval . f))
eval (App f e)     = (fst (eval f)) (eval e)
eval (Let (e :: Exp a1) e')  = let y = eval e; f = eval e'
  in reflect @a (NLet (reify @a1 y) (reify f))

----------------
-- Normalisation
----------------

norm :: Reifiable a => Exp a -> Exp a
norm = quote . eval

-----------
-- Examples
-----------

--
-- Let-sharing is respected
--

twicePlus10 :: Exp (Int -> Int)
twicePlus10 = Lam $ \ x -> 4 + x + 3 + x

largeExp :: Exp Int
largeExp = Var "IAmAnExtremelyLargeExpression"

duplicateX :: Exp Int
duplicateX = App twicePlus10 largeExp

-- *Experimental.Let> norm duplicateX
-- (IAmAnExtremelyLargeExpression + (IAmAnExtremelyLargeExpression + 7))

saveX :: Exp Int
saveX = Let largeExp twicePlus10

-- *Experimental.Let> norm saveX
-- Let IAmAnExtremelyLargeExpression in (\x0. (x0 + (x0 + 7)))

--
-- No Eta expansion happens
--

funNoEta :: Exp (Int -> Int)
funNoEta = Var "x"

funBeta :: Exp (Int -> Int)
funBeta = App (Lam id) funNoEta
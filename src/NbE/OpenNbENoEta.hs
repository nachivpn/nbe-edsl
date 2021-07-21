{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module NbE.OpenNbENoEta where

import GExp
import Control.Monad (ap, join)
import Control.Monad.State.Lazy ( join, ap, State )

import Arr ( mapArr, foldArr )

type Exp  a = GExp Reifiable a
type Prim a = GPrim Reifiable a

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
  NMul    :: ()
    => Ne Int  -> Ne Int -> Ne Int
  NRec    :: (Reifiable a)
    => (Int , Ne Int) -> (Exp Int -> Exp a -> Nf a) -> Nf a -> Ne a
  NArrLen :: (Reifiable a)
    => Ne (Arr a) -> Ne Int
  NArrIx :: (Reifiable a)
    => Ne (Arr a) -> Nf Int -> Ne a
  NLet      :: (Reifiable a, Reifiable b)
    => Nf a -> Nf (a -> b) -> Ne b
  NSave     :: (Reifiable a)
    => Exp a -> Ne a

-- normal forms, or "values" and "stuck terms (of positive types)"
data Nf a where
  NUp        :: ()
    => Ne a -> Nf a
  NLift    :: (PrimTy a)
    => a -> Nf a
  NAdd       :: ()
    => (Int , Ne Int) -> Nf Int -> Nf Int
  NUnit      :: ()
    => Nf ()
  NLam       :: (Reifiable a, Reifiable b)
    => (Exp a -> Nf b) -> Nf (a -> b)
  NPair      :: (Reifiable a, Reifiable b)
    => Nf a -> Nf b -> Nf (a,b)
  NInl       :: (Reifiable a)
    => Nf a -> Nf (Either a b)
  NInr       :: (Reifiable b)
    => Nf b -> Nf (Either a b)
  NCase      :: (Reifiable a, Reifiable b, Reifiable c)
    => Ne (Either a b) -> (Exp a -> Nf c) -> (Exp b -> Nf c) -> Nf c
  NArr       :: (Reifiable a)
    => Nf Int -> (Exp Int -> Nf a) -> Nf (Arr a)
  NGet    :: (Reifiable a, Reifiable s)
    => (Exp s -> NfStResCase s a) -> Nf (State s a)
  NPut :: (Reifiable s)
    => Nf s -> Nf (State s ())
  NRetSt_ :: (Reifiable a)
    => Nf a -> Nf (State s a)

-- Note: iso to `MDec (Nf s, NfStRes s a)`
data NfStResCase s a where
  NPutSeq :: ()
    => Nf s -> NfStRes s a -> NfStResCase s a
  NCaseSt :: (Reifiable a, Reifiable b)
    => Ne (Either a b) -> (Exp a -> NfStResCase s c) -> (Exp b -> NfStResCase s c) -> NfStResCase s c

data NfStRes s a where
  NRetSt :: (Reifiable a, Reifiable s)
    => Nf a -> NfStRes s a
  NBindSt   :: (Reifiable a, Reifiable b, Reifiable s)
    => Ne (State s a) -> (Exp a -> Nf (State s b)) -> NfStRes s b

-- embed neutrals back into expressions
embNe :: Ne a -> Exp a
embNe (NVar x)   = Var x
embNe (NApp m n) = App (embNe m) (embNf n)
embNe (NFst m)   = Fst (embNe m)
embNe (NSnd m)   = Snd (embNe m)
embNe (NMul m n) = Prim (Mul (embNe m) (embNe n))
embNe (NRec (ai,ni) f x) = Prim (Rec aini (Lam $ \ x1 -> Lam $ \ x2 -> embNf (f x1 x2)) (embNf x))
  where
    aini = if ai == 1
      then (embNe ni)
      else (Prim (Mul (Lift ai) (embNe ni)))
embNe (NArrLen n)  = ArrLen (embNe n)
embNe (NArrIx n m) = ArrIx (embNe n) (embNf m)
embNe (NLet n m)   = Let (embNf n) (embNf m)
embNe (NSave e)    = Save e

-- embed normal forms back into expressions
embNf :: Nf a -> Exp a
embNf (NUp n)                  = embNe n
embNf (NLift x)                = Lift x
-- beg. of special cases to omit trailing 0s and 1s
embNf (NAdd (1,ni) (NLift 0))  = embNe ni
embNf (NAdd (ai,ni) (NLift 0)) = Prim $ Mul (Lift ai) (embNe ni)
embNf (NAdd (1,ni) p)          = Prim $ Add (embNe ni) (embNf p)
-- end of special cases
embNf (NAdd (ai,ni) p)         = Prim $ Add (Prim $ Mul (Lift ai) (embNe ni)) (embNf p)
embNf NUnit                    = Unit
embNf (NLam f)                 = Lam (embNf . f)
embNf (NPair m n)              = Pair (embNf m) (embNf n)
embNf (NInl n)                 = Inl (embNf n)
embNf (NInr n)                 = Inr (embNf n)
embNf (NCase n f g)            = Case (embNe n) (Lam $ embNf .f) (Lam $ embNf .g)
embNf (NArr n f  )             = Arr (embNf n) (Lam $ embNf . f)
embNf (NGet f)                 = Get (Lam (go . f))
  where
    go (NPutSeq s x)   = Put (embNf s) `seqSt` embNfStRes x
    go (NCaseSt n g h) = Case (embNe n) (Lam $ go . g) (Lam $ go . h)
embNf (NPut n)                 = Put (embNf n)
embNf (NRetSt_ n)              = RetSt (embNf n)

embNfStRes :: Reifiable s => NfStRes s a -> Exp (State s a)
embNfStRes (NRetSt x)      = RetSt (embNf x)
embNfStRes (NBindSt n f)   = BindSt (embNe n) (Lam $ embNf . f)
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
  -- | "run"
  runMDec  :: MDec (Sem a) -> Sem a

-- "quote" semantics back to expressions
quote :: Reifiable a => Sem a -> Exp a
quote = embNf . reify

instance Reifiable String where
  type Sem String = Nf String
  rTypeRep        = RTString
  reify   m       = m
  reflect n       = NUp n
  runMDec m       = collect m

instance Reifiable Int where
  type Sem Int           = (MDec SOPInt,Nf Int)
  rTypeRep               = RTInt
  reify                  = snd
  reflect n              = (Leaf (SAdd (1,n) (SInt 0)) , NUp n)
  runMDec m              = (join (fst <$> m), collect (snd <$> m))

instance Reifiable () where
  type Sem () = ()
  rTypeRep    = RTUnit
  reify   ()  = NUnit
  reflect _   = ()
  runMDec m   = ()

instance  (Reifiable a, Reifiable b) => Reifiable (a,b) where
  type Sem (a,b) = ((Sem a, Sem b),Nf (a, b))
  rTypeRep       = RTProd rTypeRep rTypeRep
  reify          = snd
  reflect n      = ((reflect (NFst n), reflect (NSnd n)), NUp n)
  runMDec m      = ((runMDec @a ((fst . fst) <$> m), runMDec @b ((snd . fst) <$> m))
                  , collect (snd <$> m))

instance  (Reifiable a, Reifiable b) => Reifiable (a -> b) where
  type Sem (a -> b) = (Sem a -> Sem b, Nf (a -> b))
  rTypeRep          = RTFun rTypeRep rTypeRep
  reify             = snd
  reflect n         = (\ y -> (reflect (NApp n (reify y))), NUp n)
  runMDec m         = (\ x -> runMDec @b ((fst <$> m) <*> pure x) , collect (snd <$> m))

instance  (Reifiable a, Reifiable b) => Reifiable (Either a b) where
  type Sem (Either a b) = (MDec (Either (Sem a) (Sem b)), Nf (Either a b))
  rTypeRep              = RTSum rTypeRep rTypeRep
  reify                 = snd
  reflect n             = (SCase n (Leaf . Left . eval) (Leaf . Right . eval), NUp n)
  runMDec m             = (join (fst <$> m) , collect (snd <$> m))

instance (Reifiable a) => Reifiable (Arr a) where
  type Sem (Arr a)     = (SArr (Sem a), Nf (Arr a))
  rTypeRep             = RTArr rTypeRep
  reify                = snd
  reflect n            = (SArr (reflect @Int (NArrLen n)) (reflect @a . NArrIx n . reify . eval), NUp n)
  runMDec m            = (SArr (runMDec @Int (fmap (arrLen' . fst) m)) (runMDec @a . (<*>) (fmap (arrIx' . fst) m) . pure)
    , collect (snd <$> m))

instance (Reifiable s, Reifiable a) => Reifiable (State s a) where
  type Sem (State s a)   = (MSt s (Sem a), Nf (State s a))
  rTypeRep               = RTState rTypeRep rTypeRep
  reify                  = snd
  reflect n              = (MSt $ \ s -> Leaf (s, SBindSt n (embRes . SRetSt . eval)), NUp n)
  runMDec m              = (collectState (fst <$> m) , collect (snd <$> m))
    where
    -- "collect" state comp. stuck under case distinction
    collectState :: MDec (MSt s sa) -> MSt s sa
    collectState (Leaf x)       = x
    collectState (SCase n f g) = sCaseState n (collectState . f) (collectState . g)

-------------
-- Evaluation
-------------

-- NOTE: the <$> and <*> are caused by the monad MDec on SOPInt
evalPrim :: forall a . Reifiable a
  => Prim a -> Sem a
evalPrim (Mul e1 e2) = let (mx,x) = eval e1; (my,y) = eval e2 ; z = mul' <$> mx <*> my
  in (z , collect $ fmap reifySOPInt z)
evalPrim (Add e1 e2) = let (mx,x) = eval e1; (my,y) = eval e2 ; z = add' <$> mx <*> my
  in (z , collect $ fmap reifySOPInt z)
evalPrim (Rec n f a) = runMDec @a $
  rec' @a
    <$> (fst $ eval n)
    <*> return ((.) fst . fst $ eval f)
    <*> return (eval a)

eval :: forall a . Reifiable a
  => Exp a -> Sem a
eval (Var s)       = reflect @a (NVar s)
eval Unit          = ()
eval (Lift x)      = drown x
eval (Prim p)      = evalPrim p
eval (Lam f)       = (eval . f . quote , NLam (reify . eval . f))
eval (App f e)     = (fst (eval f)) (eval e)
eval (Pair e e')   = let x = eval e; y = eval e'
  in ((x , y), NPair (reify x) (reify y))
eval (Fst e)       = fst . fst . eval $ e
eval (Snd e)       = snd . fst . eval $ e
eval (Inl e)       = let x = eval e in
  (Leaf (Left x), NInl (reify x))
eval (Inr e)       = let x = eval e in
  (Leaf (Right x), NInr (reify x))
eval (Case e f g)  = let
  (x,_)  = eval e;
  (f',_) = eval f;
  (g',_) = eval g in
  runMDec @a (either f' g' <$> x)
eval (Arr e e')    = let n = eval e; y = eval e' in
  (SArr n ((fst y) . eval),NArr (reify n) (reify .fst y . eval))
eval (ArrLen e)    = arrLen' (fst $ eval e)
eval (ArrIx e e')  = arrIx' (fst $ eval e) e'
eval (Let (e :: Exp a1) e')  = let y = eval e; f = eval e'
  in reflect @a (NLet (reify @a1 y) (reify f))
eval (Save e)  = reflect @a (NSave e)
eval (Get e)   = let {
    (f,nf) = eval e ;
    x = get' >>= (fst . f)}
  in (x, reifySt x)
eval (Put e) = let x = eval e
  in (put' x, NPut (reify x))
eval (RetSt e)     = let x = eval e
  in (return x , NRetSt_ (reify x))
eval (BindSt e e') = let {
    (m,_) = eval e ;
    mf    = runMState m ;
    (g,_) = eval e' ;
    x     = m >>= (fst . g)}
  in (x , reifySt x)
eval _ = error "Err is TBD!"

-- insert primitive values into semantics
drown :: forall a . PrimTy a => a -> Sem a
drown = go (pTypeRep @a)
  where
    go :: forall a . PTypeRep a -> a -> Sem a
    go PTInt    x = (Leaf (SInt x),NLift x)
    go PTString x = NLift x

----------------
-- Normalisation
----------------

norm :: Reifiable a => Exp a -> Exp a
norm = quote . eval

------------------------
-- Semantics of integers
------------------------

-- semantics of integers take the shape of "sum of products":
-- (a_0 * x_0) + (a_1 * x_1) + ..... + a_n
-- where, for each i, `a_i` is a constant, and `x_i` is a neutral
data SOPInt where
  -- a_n
  SInt :: ()
    => Int -> SOPInt
  -- (a_i * x_i) + ...
  -- Invariant: a_i must not be a 0!
  SAdd :: ()
    => (Int , Ne Int) -> SOPInt -> SOPInt

-- SOPInt can be reified to integers (in normal form)
reifySOPInt :: SOPInt -> Nf Int
reifySOPInt (SInt a0)        = NLift a0
reifySOPInt (SAdd (ai,ni) p) = NAdd (ai,ni) (reifySOPInt p)

-- addition on SOPInt
add' :: SOPInt -> SOPInt -> SOPInt
add' (SInt 0)       p
  = p
add' (SInt a0)      (SInt b0)
  = SInt (a0 + b0)
add' (SInt a0)      (SAdd bimi p)
  = SAdd bimi (add' (SInt a0) p)
add' (SAdd aini ans) p
  = SAdd aini (add' ans p)

-- multiplication on SOPInt
mul' :: SOPInt -> SOPInt -> SOPInt
mul' (SInt 0)            _
  = SInt 0
mul' (SInt 1)            p
  = p
mul' (SInt a0)           (SInt b0)
  = SInt (a0 * b0)
mul' (SInt a0)           (SAdd (bi,mi) p)
  | a0*bi == 0 = mul' (SInt a0) p
  | otherwise  = SAdd (a0 * bi ,mi) (mul' (SInt a0) p)
mul' (SAdd (ai,ni) ans)  (SInt b0)
  | ai*b0 == 0 = (mul' ans (SInt b0))
  | otherwise  = SAdd (ai * b0 , ni) (mul' ans (SInt b0))
mul' (SAdd (ai,ni) p)    (SAdd (bi,mi) q)
  | ai*bi == 0 = mul' (SAdd (ai,ni) p) q
  | otherwise  = SAdd (ai * bi , NMul ni mi) (mul' (SAdd (ai,ni) p) q)

-- recursion using SOPInt
rec'  :: forall a . Reifiable a => SOPInt -> (Sem Int -> Sem a -> Sem a) -> Sem a -> Sem a
rec' (SInt x)      f a
  | x <= 0    = a
  | otherwise = rec' @a (SInt (x - 1)) f (f (return (SInt x), NLift x) a)
rec' (SAdd aini p) f a = reflect @a (NRec aini f' a')
    where
      f' :: Exp Int -> Exp a -> Nf a
      f' i b = reify (f (eval i) (eval b))
      a' :: Nf a
      a' = reify (rec' @a p f a)

--------------------
-- Semantics of sums
--------------------

-- A "Decision tree" monad to record case
-- distinctions on stuck terms of a sum type.
data MDec a where
  Leaf  ::  ()
    => a -> MDec a
  SCase  :: (Reifiable a, Reifiable b)
    => Ne (Either a b) -> (Exp a -> MDec c) -> (Exp b -> MDec c) -> MDec c

collect :: forall a. (Reifiable a) => MDec (Nf a) -> Nf a
collect (Leaf x)       = x
collect (SCase n f g) = NCase n (collect . f) (collect . g)

instance Functor MDec where
  fmap f (Leaf x)       = Leaf (f x)
  fmap f (SCase n g h) = SCase n (fmap f . g) (fmap f . h)

instance Applicative MDec where
  pure  = Leaf
  (<*>) = ap

instance Monad MDec where
  return x             = Leaf x
  (Leaf x)       >>= f = f x
  (SCase n g h) >>= f = SCase n ((=<<) f . g) ((=<<) f . h)

--------------------------
-- Semantics of exceptions
--------------------------

-- A (semantic) "Error" monad to record binding and case
-- distinctions on stuck terms of a monadic type.
data MErr a where
  SRetErr     :: ()
    => a -> MErr a
  SThrow      :: ()
    => Nf String -> MErr a
  SCBindErr  :: (Reifiable a)
    => Ne (Err a)
      -> (Exp a -> MErr b)
      -> (Exp String -> MErr b)
      -> MErr b
  SCaseErr     :: (Reifiable a, Reifiable b)
    => Ne (Either a b)
      -> (Exp a -> MErr c)
      -> (Exp b -> MErr c)
      -> MErr c

throw' :: Sem String -> MErr a
throw' = SThrow

catch' :: MErr sa -> (Sem String -> MErr sa) -> MErr sa
catch' (SRetErr x)       f = SRetErr x
catch' (SThrow x)        f = f x
catch' (SCBindErr n g h) f = SCBindErr n (flip catch' f . g) (flip catch' f . h)
catch' (SCaseErr n g h)  f = SCaseErr n (flip catch' f . g) (flip catch' f . h)

instance Functor MErr where
  fmap f (SRetErr x)       = SRetErr (f x)
  fmap f (SThrow x)        = SThrow x
  fmap f (SCBindErr n g h) = SCBindErr n (fmap f . g) (fmap f . h)
  fmap f (SCaseErr n g h)  = SCaseErr n (fmap f . g) (fmap f . h)

instance Applicative MErr where
  pure  = SRetErr
  (<*>) = ap

instance Monad MErr where
  return x                = SRetErr x
  (SRetErr x)       >>= f = f x
  (SThrow x)        >>= f = SThrow x
  (SCBindErr n g h) >>= f = SCBindErr n ((=<<) f  . g) ((=<<) f . h)
  (SCaseErr n g h)  >>= f = SCaseErr n ((=<<) f  . g) ((=<<) f . h)

---------------------
-- Semantics of State
---------------------

-- MSt monad (MSt s :: * -> *)

newtype MSt s a = MSt {runMState :: (Sem s) -> MDec (Sem s , MStRes s a)}

sCaseState :: (Reifiable a, Reifiable b)
    => Ne (Either a b)
      -> (Exp a -> MSt s c)
      -> (Exp b -> MSt s c)
      -> MSt s c
sCaseState n f g = MSt $ \ s -> SCase n (flip runMState s . f) (flip runMState s . g)

data MStRes s a where
  SRetSt  :: ()
    => a -> MStRes s a
  SBindSt :: (Reifiable a)
    => Ne (State s a) -> (Exp a -> MSt s b) -> MStRes s b

get' :: MSt s (Sem s)
get' = MSt $ \ s -> Leaf (s , SRetSt s)

put' :: (Sem s) -> MSt s ()
put' s = MSt $ \ _ -> Leaf (s, SRetSt ())

embRes :: MStRes s a -> MSt s a
embRes x = MSt $ \s -> Leaf (s, x)

reifySt :: (Reifiable a, Reifiable s) => MSt s (Sem a) -> Nf (State s a)
reifySt m = NGet (collectNfSt
    . fmap (mapTup reify reifyMStRes)
    . runMState m
    . eval)
    where
      collectNfSt :: MDec (Nf s, NfStRes s a) -> NfStResCase s a
      collectNfSt (Leaf (n,x))  = NPutSeq n x
      collectNfSt (SCase n g h) = NCaseSt n (collectNfSt . g) (collectNfSt . h)
      reifyMStRes :: (Reifiable a, Reifiable s) => MStRes s (Sem a) -> NfStRes s a
      reifyMStRes (SRetSt x)    = NRetSt (reify x)
      reifyMStRes (SBindSt n f) = NBindSt n (reifySt . f)

-- mutually recursive Functor instances
instance Functor (MSt s) where
  fmap f m = MSt $ fmap (fmap (fmap f)) . runMState m

instance Functor (MStRes s) where
  fmap f (SRetSt x)      = SRetSt (f x)
  fmap f (SBindSt n g)   = SBindSt n (fmap @(MSt s) f . g)

instance Applicative (MSt s) where
  pure = return; (<*>) = ap

-- implementing join is much more illuminating than >>=
joinMState :: MSt s (MSt s a) -> MSt s a
joinMState m = MSt $ (=<<) magic . runMState m

magic :: (Sem s , MStRes s (MSt s a)) -> MDec (Sem s , MStRes s a)
magic (s, SRetSt m)      = runMState m s
magic (s, SBindSt n g)   = Leaf (s, SBindSt n (joinMState . g))

instance Monad (MSt s) where
  return  x = MSt $ \s -> Leaf (s, SRetSt x)
  m >>= f   = joinMState (fmap f m)

----------------------
-- Semantics of Arrays
----------------------

data SArr a where
  SArr :: Sem Int -> (Exp Int -> a) -> SArr a

arrLen' :: SArr a -> Sem Int
arrLen' (SArr n _) = n

arrIx' :: SArr a -> Exp Int -> a
arrIx' (SArr _ f) e = f e


instance Functor SArr where
  fmap f (SArr n g) = SArr n (f . g)

-----------
-- Examples
-----------

funNoEta :: Exp (String -> String)
funNoEta = Var "x"

funBeta :: Exp (String -> String)
funBeta = App (Lam id) funNoEta

sumNoEta :: Exp (Either String String)
sumNoEta = Var "x"

sumBeta :: Exp (String -> String -> String)
sumBeta = Lam $ \s -> Lam $ \ s' -> Case (Inl s) (Lam id) (Lam id)

sumComm :: Exp (Either String String -> String)
sumComm = Lam $ \s -> Fst (Case s
  (Lam $ \ x -> Pair x x)
  (Lam $ \ x -> Pair x x))

-- length of known array
exar1 :: Exp Int
exar1 = ArrLen (Arr 5 (Lam $ id))

-- index into known array
exar2 :: Exp Int
exar2 = ArrIx (Arr 5 (Lam $ const 20)) 1

-- map fusion
exar3 :: Exp (Arr Int -> Arr Int)
exar3 = Lam $ \ arr -> mapArr (Lam (+ 2)) (mapArr (Lam (+ 1)) arr)

-- map-fold fusion
exar4 :: Exp (Arr Int -> Int)
exar4 = Lam $ \ arr ->
  foldArr
    (Lam $ \ acc -> Lam $ \ x -> acc + x)
    0
    (mapArr (Lam (+ 1)) arr)

-- map fusion with case
exar5 :: Exp (BoolE -> Arr Int -> Arr Int)
exar5 = Lam $ \ scr -> Lam $ \ arr ->
    mapArr (Lam (+ 2)) $
      Case scr
        (Lam $ \ _ -> mapArr (Lam (+ 1)) arr)
        (Lam $ \ _ -> mapArr (Lam (+ 2)) arr)

double :: Exp (Int -> Int)
double = Lam $ \ x -> x + x

doubleHeavy :: Exp Int
doubleHeavy = App double (Var "heavy")

exDoubleApp' :: Exp Int
exDoubleApp' = Let (Var "heavy" :: Exp Int) double

doubleHeavy' :: Exp Int
doubleHeavy' = Save doubleHeavy

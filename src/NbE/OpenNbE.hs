{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module NbE.OpenNbE where

import GExp
import Control.Monad (ap, join)
import Control.Monad.State.Lazy ( join, ap, State, evalState )

type Exp  a = GExp Reifiable a
type Prim a = GPrim Reifiable a

---------------
-- Normal forms
---------------

-- neutrals, or "stuck terms"
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

-- normal forms
data Nf a where
  NUp        :: ()
    => Ne String -> Nf String
  NInt       :: ()
    => Int -> Nf Int
  NString    :: ()
    => String -> Nf String
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
  NRetErr    :: (Reifiable a)
    => Nf a -> Nf (Err a)
  NThrow     :: ()
    => Nf String -> Nf (Err a)
  NCatchBind :: (Reifiable a, Reifiable b)
    => Ne (Err a) -> (Exp a -> Nf (Err b)) -> (Exp String -> Nf (Err b)) -> Nf (Err b)
  NGet    :: (Reifiable a, Reifiable s)
    => (Exp s -> NfStResCase s a) -> Nf (State s a)
  NArr      :: (Reifiable a)
    => Nf Int -> (Exp Int -> Nf a) -> Nf (Arr a)

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
embNf (NInt x)                 = Lift x
embNf (NString x)              = Lift x
-- beg. of special cases to omit trailing 0s and 1s
embNf (NAdd (1,ni) (NInt 0))   = embNe ni
embNf (NAdd (ai,ni) (NInt 0))  = Prim $ Mul (Lift ai) (embNe ni)
embNf (NAdd (1,ni) p)          = Prim $ Add (embNe ni) (embNf p)
-- end of special cases
embNf (NAdd (ai,ni) p)         = Prim $ Add (Prim $ Mul (Lift ai) (embNe ni)) (embNf p)
embNf NUnit                    = Unit
embNf (NLam f)                 = Lam (embNf . f)
embNf (NPair m n)              = Pair (embNf m) (embNf n)
embNf (NInl n)                 = Inl (embNf n)
embNf (NInr n)                 = Inr (embNf n)
embNf (NCase n f g)            = Case (embNe n) (Lam $ embNf .f) (Lam $ embNf .g)
embNf (NRetErr n)              = RetErr (embNf n)
embNf (NThrow n)               = Throw (embNf n)
embNf (NCatchBind n f g)       = Catch (BindErr (embNe n) (Lam $ embNf . f)) (Lam $ embNf . g)
embNf (NGet f)                 = Get (Lam (go . f))
  where
    go (NPutSeq s x)   = Put (embNf s) `seqSt` embNfStRes x
    go (NCaseSt n g h) = Case (embNe n) (Lam $ go . g) (Lam $ go . h)
embNf (NArr n f)               = Arr (embNf n) (Lam $ embNf . f)

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

-- "quote" semantics back to expressions
quote :: Reifiable a => Sem a -> Exp a
quote = embNf . reify

instance Reifiable String where
  type Sem String = MDec (Either (Ne String) String)
  rTypeRep   = RTString
  reify m    = collectNf (fmap (either NUp NString) m)
  reflect n  = Leaf (Left n)

instance Reifiable () where
  type Sem () = ()
  rTypeRep    = RTUnit
  reify   ()  = NUnit
  reflect _   = ()

instance  (Reifiable a, Reifiable b) => Reifiable (a,b) where
  type Sem (a,b) = (Sem a, Sem b)
  rTypeRep       = RTProd rTypeRep rTypeRep
  reify   (x,y)  = NPair (reify x) (reify y)
  reflect n      = (reflect (NFst n), reflect (NSnd n))

instance  (Reifiable a, Reifiable b) => Reifiable (a -> b) where
  type Sem (a -> b) = Sem a -> Sem b
  rTypeRep          = RTFun rTypeRep rTypeRep
  reify f           = NLam (\e -> reify (f (eval e)))
  reflect n         = \ y -> (reflect (NApp n (reify y)))

instance  (Reifiable a, Reifiable b) => Reifiable (Either a b) where
  type Sem (Either a b)   = MDec (Either (Sem a) (Sem b))
  rTypeRep                = RTSum rTypeRep rTypeRep
  reify  (Leaf (Left x))  = NInl (reify x)
  reify  (Leaf (Right x)) = NInr (reify x)
  reify  (SCase n f g)    = NCase n (reify . f) (reify . g)
  reflect n               = SCase n (Leaf . Left . eval) (Leaf . Right . eval)

instance Reifiable Int where
  type Sem Int           = MDec SOPInt
  rTypeRep               = RTInt
  reify                  = collectNf . remRedGuards . fmap reifySOPInt
  reflect n              = Leaf (SAdd (1,n) (SInt 0))

instance (Reifiable a) => Reifiable (Err a) where
  type Sem (Err a)        = MErr (Sem a)
  rTypeRep                = RTErr rTypeRep
  reify (SRetErr x)       = NRetErr (reify x)
  reify (SThrow n)        = NThrow (reify n)
  reify (SCBindErr n f g) = NCatchBind n (reify . f) (reify . g)
  reify (SCaseErr n f g)  = NCase n (reify . f) (reify . g)
  reflect n               = SCBindErr n (SRetErr . eval) (SThrow .eval)

instance (Reifiable s, Reifiable a) => Reifiable (State s a) where
  type Sem (State s a)   = MSt s (Sem a)
  rTypeRep               = RTState rTypeRep rTypeRep
  reify m                = NGet (collectNfStRes
      . fmap (mapTup reify reifyMStRes)
      . runMState m
      . eval)
    where
    --
    collectNfStRes :: MDec (Nf s, NfStRes s a) -> NfStResCase s a
    collectNfStRes (Leaf (n,x))  = NPutSeq n x
    collectNfStRes (SCase n g h) = NCaseSt n (collectNfStRes . g) (collectNfStRes . h)
    --
    reifyMStRes :: MStRes s (Sem a) -> NfStRes s a
    reifyMStRes (SRetSt x)    = NRetSt (reify x)
    reifyMStRes (SBindSt n f) = NBindSt n (reify . f)
  reflect n              = MSt $ \ s -> Leaf (s, SBindSt n (embRes . SRetSt . eval))

instance (Reifiable a) => Reifiable (Arr a) where
  type Sem (Arr a)     = SArr (Sem a)
  rTypeRep             = RTArr rTypeRep
  reify (SArr n f)     = NArr (reify @Int n) (reify @a . f)
  reflect x            = SArr (reflect @Int (NArrLen x)) (reflect @a . NArrIx x . reify . eval)

-------------
-- Evaluation
-------------

-- NOTE: the <$> and <*> are caused by the monad MDec on SOPInt
evalPrim :: forall a . Reifiable a => Prim a -> Sem a
evalPrim (Mul e1 e2) = mul' <$> (eval e1) <*> (eval e2)
evalPrim (Add e1 e2) = add' <$> (eval e1) <*> (eval e2)
evalPrim (Rec n f a) = runMDec @a $
  rec' @a
    <$> eval n
    <*> return (eval f)
    <*> return (eval a)

eval :: forall a . Reifiable a => Exp a -> Sem a
eval (Var s)       = reflect @a (NVar s)
eval Unit          = ()
eval (Lift x)      = drown x
eval (Prim p)      = evalPrim p
eval (Lam f)       = \ x -> eval (f (quote x))
eval (App f e)     = (eval f) (eval e)
eval (Pair e e')   = (eval e , eval e')
eval (Fst e)       = fst (eval e)
eval (Snd e)       = snd (eval e)
eval (Inl e)       = return (Left (eval e))
eval (Inr e)       = return (Right (eval e))
eval (Case s f g)  = let
  s' = eval s;
  f' = eval f;
  g' = eval g in
  runMDec @a (either f' g' <$> s')
eval (RetErr e)    = return (eval e)
eval (BindErr e f) = eval e >>= eval f
eval (Throw e)     = throw' (eval e)
eval (Catch e f)   = catch' (eval e) (eval f)
eval (Get e)       = get' >>= eval e
eval (Put e)       = put' (eval e)
eval (RetSt e)     = return (eval e)
eval (BindSt e e') = eval e >>= eval e'
eval (Arr e e')    = SArr (eval e) (eval e' . eval)
eval (ArrLen e)    = arrLen' (eval e)
eval (ArrIx e e')  = arrIx' (eval e) e'
eval (Let (e :: Exp a1) e')
                   = let y = eval e; f = eval e'
                     in reflect @a (NLet (reify @a1 y) (reify f))
eval (Save e)      = reflect @a (NSave e)

-- insert primitive values into semantics
drown :: forall a . PrimTy a => a -> Sem a
drown = go (pTypeRep @a)
  where
    go :: forall a . PTypeRep a -> a -> Sem a
    go PTInt    x = Leaf (SInt x)
    go PTString x = Leaf (Right x)

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
reifySOPInt (SInt a0)        = NInt a0
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
  | otherwise = rec' @a (SInt (x - 1)) f (f (return (SInt x)) a)
rec' (SAdd aini p) f a = reflect @a (NRec aini f' a')
    where
      -- f' :: Exp Int -> Exp a -> Nf a
      f' i b = reify (f (eval i) (eval b))
      -- a' :: Nf a
      a' = reify (rec' @a p f a)

--------------------
-- Semantics of sums
--------------------

-- A "Case Tree" monad to record case
-- distinctions on stuck terms of a sum type.
data MDec a where
  Leaf    ::  ()
    => a -> MDec a
  SCase   :: (Reifiable a, Reifiable b)
    => Ne (Either a b) -> (Exp a -> MDec c) -> (Exp b -> MDec c) -> MDec c

-- enables extraction of result of a case distinction (used for evaluating Case)
runMDec :: forall a . Reifiable a => MDec (Sem a) -> Sem a
runMDec = go (rTypeRep @a)
  where
    -- auxiliary function for runMDec which receives induction parameter
    go :: forall a . RTypeRep Reifiable a -> MDec (Sem a) -> Sem a
    go RTUnit        _ = ()
    go RTInt         m = join m
    go (RTProd a b)  m = (go a (fmap fst m), go b (fmap snd m))
    go (RTFun _ b)   m = \ x -> go b (m <*> (pure x))
    go (RTSum _ _)   m = join m
    go (RTErr _)     m = collectErr m
    go RTString      m = join m
    go (RTState s a) m = collectState m
    go (RTArr (a1 :: RTypeRep Reifiable a1))     m
      = SArr (runMDec @Int (fmap arrLen' m)) (runMDec @a1 . (<*>) (fmap arrIx' m) . pure)

collectNf :: Reifiable a => MDec (Nf a) -> Nf a
collectNf (Leaf x)       = x
collectNf (SCase n f g) = NCase n (collectNf . f) (collectNf . g)

-- "collect" errors stuck under case distinction
collectErr :: MDec (MErr sa) -> MErr sa
collectErr (Leaf x)       = x
collectErr (SCase n f g) = SCaseErr n (collectErr . f) (collectErr . g)

-- "collect" state comp. stuck under case distinction
collectState :: MDec (MSt s sa) -> MSt s sa
collectState (Leaf x)       = x
collectState (SCase n f g) = sCaseState n (collectState . f) (collectState . g)

instance Functor MDec where
  fmap f (Leaf x)      = Leaf (f x)
  fmap f (SCase n g h) = SCase n (fmap f . g) (fmap f . h)

instance Applicative MDec where
  pure  = Leaf
  (<*>) = ap

instance Monad MDec where
  return x             = Leaf x
  (Leaf x)      >>= f = f x
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
    => Sem String -> MErr a
  SCBindErr   :: (Reifiable a)
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

------------------------------
-- Optimizing Case expressions
------------------------------

eqMDecSt :: MDec (Nf a) -> MDec (Nf a) -> St Bool
eqMDecSt (Leaf x)      (Leaf y)
  = eqGExpSt (embNf x) (embNf y)
eqMDecSt (SCase n f g) (SCase n' f' g')
  = do
    b1 <- eqGExpSt (embNe n) (embNe n')
    x <- freshCmp
    b2 <- eqMDecSt (f (Var x)) (f' (Var x))
    y <- freshCmp
    b3 <- eqMDecSt (g (Var y)) (g' (Var y))
    return $ b1 && b2 && b3
eqMDecSt _ _
  = return False

instance Eq (MDec (Nf a)) where
  m == m' = evalState (eqMDecSt m m') 0

remRedGuards :: MDec (Nf a) -> MDec (Nf a)
remRedGuards (Leaf x) = Leaf x
remRedGuards b@(SCase n f g)
  -- if these two functions yield same result when applied to
  -- different arguments, then they both don't use the argument
  | f (Var "_y") == g (Var "_z") = remRedGuards (f (Var "_"))
  | otherwise = b

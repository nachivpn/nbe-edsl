{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleInstances #-}
module GExp where

import Prelude hiding ((<>))
import Data.Constraint (Constraint)
import Text.PrettyPrint
import Text.PrettyPrint.HughesPJClass hiding (pPrintList)
import Control.Monad.State.Lazy

import Control.Monad.Except (Except)
import Data.Array ( Array )

--------------
-- Expressions
--------------

-- Type aliases
type Err = Except String
type Arr = Data.Array.Array Int

-- Primitive types
class Eq a => PrimTy a where
  pTypeRep :: PTypeRep a

instance PrimTy Int where
  pTypeRep = PTInt

instance PrimTy String where
  pTypeRep = PTString

-- Primitive operations
data GPrim (c :: * -> Constraint) a where
  Mul  :: GExp c Int -> GExp c Int          -> GPrim c Int
  Add  :: GExp c Int -> GExp c Int          -> GPrim c Int
  Rec  :: (c a) => GExp c Int -> GExp c (Int -> a -> a) -> GExp c a -> GPrim c a

-- Higher-order abstract syntax for expressions
--
-- `GExp c a` is an expression of type a, where
-- `c` is the constraint that all type variables in the def. are subject to
-- e.g., `GExp Reifiable Int` denotes integer expressions where
-- all "intermediate" type variables are subject to the contraint `Reifiable`.
--

data GExp (c :: * -> Constraint) a where
  -- Variables/Unknowns
  Var      :: c a
    => String -> GExp c a
  -- Constants and primitives
  Lift     :: PrimTy a
    => a -> GExp c a
  Prim     :: ()
    => GPrim c a -> GExp c a
  -- Functions
  Lam      :: (c a, c b)
    => (GExp c a -> GExp c b) -> GExp c (a -> b)
  App      :: (c a)
    => GExp c (a -> b) -> GExp c a -> GExp c b
  -- Products
  Unit     :: ()
    => GExp c ()
  Pair     :: (c a, c b)
    => GExp c a -> GExp c b -> GExp c (a,b)
  Fst      :: (c b)
    => GExp c (a,b) -> GExp c a
  Snd      :: (c a)
    => GExp c (a,b) -> GExp c b
  -- Sums
  Inl      :: (c a)
    => GExp c a -> GExp c (Either a b)
  Inr      :: (c b)
    => GExp c b -> GExp c (Either a b)
  Case     :: (c a, c b, c d)
    => GExp c (Either a b) -> GExp c (a -> d) -> GExp c (b -> d) -> GExp c d
  -- Exceptions
  RetErr   :: (c a)
    => GExp c a -> GExp c (Err a)
  BindErr  :: (c a)
    => GExp c (Err a) -> GExp c (a -> Err b) -> GExp c (Err b)
  Throw    :: ()
    => GExp c String -> GExp c (Err a)
  Catch    :: ()
    => GExp c (Err a) -> GExp c (String -> Err a) -> GExp c (Err a)
  -- State
  Get      :: (c a, c s)
    => GExp c (s -> State s a) -> GExp c (State s a)
  Put      :: (c s)
    => GExp c s -> GExp c (State s ())
  RetSt    :: (c a)
    => GExp c a -> GExp c (State s a)
  BindSt   :: (c a, c b , c s)
    => GExp c (State s a) -> GExp c (a -> State s b) -> GExp c (State s b)
  -- Arrays
  Arr      :: (c a)
    => GExp c Int -> GExp c (Int -> a) -> GExp c (Arr a)
  ArrLen   :: (c a)
    => GExp c (Arr a) -> GExp c Int
  ArrIx    :: ()
    => GExp c (Arr a) -> GExp c Int -> GExp c a
  -- Primitives to manually tame code explosion
  Let      :: (c a, c b)
    => GExp c a -> GExp c (a -> b) -> GExp c b
  Save     :: (c a)
    => GExp c a -> GExp c a

-----------------------------------
-- Type reps for induction on types
-----------------------------------

-- Rep. of "primitive" types
data PTypeRep a where
  PTInt    :: PTypeRep Int
  PTString :: PTypeRep String

-- Rep. of "reifiable" types
data RTypeRep c a where
  RTUnit   :: (c ())     => RTypeRep c ()
  RTInt    :: (c Int)    => RTypeRep c Int
  RTString :: (c String) => RTypeRep c String
  RTProd   :: (c a, c b) => RTypeRep c a -> RTypeRep c b -> RTypeRep c (a , b)
  RTSum    :: (c a, c b) => RTypeRep c a -> RTypeRep c b -> RTypeRep c (Either a b)
  RTFun    :: (c a, c b) => RTypeRep c a -> RTypeRep c b -> RTypeRep c (a -> b)
  RTErr    :: (c a)      => RTypeRep c a -> RTypeRep c (Err a)
  RTState  :: (c a, c s) => RTypeRep c s -> RTypeRep c a -> RTypeRep c (State s a)
  RTArr    :: (c a)      => RTypeRep c a -> RTypeRep c (Arr a)

------------------
-- Pretty printing
------------------

pPrintPrimTy :: PrimTy a => a -> Doc
pPrintPrimTy x = go pTypeRep x
  where
    go :: PTypeRep a -> a -> Doc
    go PTInt    x = pPrint x
    go PTString x = pPrint x

type St = State Int

fresh :: String -> St String
fresh x = do
  n <- get
  put (n + 1)
  return (x ++ show n)

freshPrint :: St String
freshPrint = fresh "x"

pPrintPrim :: GPrim c a -> St Doc
pPrintPrim (Mul t u) = do
  t' <- pPrintExp t
  u' <- pPrintExp u
  return $ lparen
    <> t' <+> char '*' <+> u'
    <> rparen
pPrintPrim (Add t u) = do
  t' <- pPrintExp t
  u' <- pPrintExp u
  return $ lparen
    <> t' <+> char '+' <+> u'
    <> rparen
pPrintPrim (Rec n f t) = do
  n' <- pPrintExp n
  f' <- pPrintExp f
  t' <- pPrintExp t
  return $ lparen <> text "rec" <+> n' <+> f' <+> t' <> rparen

pPrintExp :: GExp c a -> St Doc
pPrintExp (Var s)     = return (text s)
pPrintExp (Lift x)    = return (pPrintPrimTy x)
pPrintExp (Prim p)    = pPrintPrim p
pPrintExp Unit        = return (pPrint ())
pPrintExp (Lam f)     = do
  x <- freshPrint
  fx' <- pPrintExp (f (Var x))
  return $ lparen
    <> (text "\\") <> text x <> char '.' <+> fx'
    <> rparen
pPrintExp (App f u)   = do
  f' <- pPrintExp f
  u' <- pPrintExp u
  return $ f' <+> u'
pPrintExp (Pair t u)   = do
  t' <- pPrintExp t
  u' <- pPrintExp u
  return $
    lparen
      <> t' <> comma <> u'
    <> rparen
pPrintExp (Fst t)      =
  (text "fst" <+>) <$> pPrintExp t
pPrintExp (Snd t)      =
  (text "snd" <+>) <$> pPrintExp t
pPrintExp (Inl t)      =
  (text "inl" <+>) <$> pPrintExp t
pPrintExp (Inr t)      =
  (text "inr" <+>) <$> pPrintExp t
pPrintExp (Case s f g) = do
  s' <- pPrintExp s
  f' <- pPrintExp f
  g' <- pPrintExp g
  return $ text "Case" <+> (lparen <> s' <> rparen) <+> text "of"
        $$ nest 2 (text "inl ->" <+> f')
        $$ nest 2 (text "inr ->" <+> g')
pPrintExp (RetErr t)    =
  (text "return" <+>) <$> pPrintExp t
pPrintExp (BindErr t u) = do
  t' <- pPrintExp t
  u' <- pPrintExp u
  return $ t' <+> text ">>=" <+> u'
pPrintExp (Throw t)    =
  (text "throw" <+>) <$> pPrintExp t
pPrintExp (Catch t u)  = do
  t' <- pPrintExp t
  u' <- pPrintExp u
  return $ text "catch"
    $$ nest 2 (lparen <> t' <> rparen)
    $$ nest 2 u'
pPrintExp (RetSt t)    =
  (text "return" <+>) <$> pPrintExp t
pPrintExp (BindSt t u) = do
  t' <- pPrintExp t
  u' <- pPrintExp u
  return $ t' <+> text ">>=" <+> u'
pPrintExp (Get t)   =do
  t' <- pPrintExp t
  return $ text "get >>=" <+> t'
pPrintExp (Put t)  = do
  t' <- pPrintExp t
  -- u' <- pPrintExp u
  return $ text "put" <+> t'
pPrintExp (Arr t u) = do
  t' <- pPrintExp t
  u' <- pPrintExp u
  return $ text "newArr" <+> t' <+> u'
pPrintExp (ArrLen t) = do
  t' <- pPrintExp t
  return $ text "length" <> lparen <> t' <> rparen
pPrintExp (ArrIx t u) = do
  t' <- pPrintExp t
  u' <- pPrintExp u
  return $ lparen <> t' <+> text "!" <+> u' <> rparen
pPrintExp (Let t u)   = do
  t' <- pPrintExp t
  u' <- pPrintExp u
  return $ text "Let" <+> t' <+> text "in" <+> u'
pPrintExp (Save t) = do
  t' <- pPrintExp t
  return $ text "Save" <> lparen <> t' <> rparen

instance Pretty (GExp c a) where
  pPrint e = evalState (pPrintExp e) 0

instance Show (GExp c a) where
  show = show . pPrint

--------------------
-- Equality checking
--------------------

-- Hack alert: we'll pretend that variables beg. with "_" are fresh

freshCmp :: St String
freshCmp = fresh "_"

eqGPrim :: GPrim c a -> GPrim c b -> St Bool
eqGPrim (Mul t u) (Mul t' u')
  = do
    b1 <- eqGExpSt t t'
    b2 <- eqGExpSt u u'
    return $ b1 && b2
eqGPrim (Add t u) (Add t' u')
  = do
    b1 <- eqGExpSt t t'
    b2 <- eqGExpSt u u'
    return $ b1 && b2
eqGPrim (Rec n f t)  (Rec n' f' t')
  = do
    b1 <- eqGExpSt n n'
    b2 <- eqGExpSt f' f'
    b3 <- eqGExpSt t t'
    return $ b1 && b2 && b3
eqGPrim _ _
  = return False

eqGExpSt :: GExp c a -> GExp c b -> St Bool
eqGExpSt (Var s) (Var s')
  = return $ s == s'
eqGExpSt (Lift x) (Lift x')
  = return $ go pTypeRep pTypeRep x x'
    where
    go :: PTypeRep a -> PTypeRep b -> a -> b -> Bool
    go PTInt    PTInt    x x' = x == x'
    go PTString PTString x x' = x == x'
    go _        _        _ _  = False
eqGExpSt (Prim p) (Prim p')
  = eqGPrim p p'
eqGExpSt Unit Unit
  = return True
eqGExpSt (Lam f) (Lam f')
  = do
    x <- freshCmp
    eqGExpSt (f (Var x)) (f' (Var x))
eqGExpSt (App f u) (App f' u')
  = do
    b1 <- eqGExpSt f f'
    b2 <- eqGExpSt u u'
    return $ b1 && b2
eqGExpSt (Pair t u) (Pair t' u')
  = do
    b1 <- eqGExpSt t t'
    b2 <- eqGExpSt u u'
    return $ b1 && b2
eqGExpSt (Fst t) (Fst t')
  = eqGExpSt t t'
eqGExpSt (Snd t) (Snd t')
  = eqGExpSt t t'
eqGExpSt (Inl t) (Inl t')
  = eqGExpSt t t'
eqGExpSt (Inr t) (Inr t')
  = eqGExpSt t t'
eqGExpSt (Case s f g) (Case s' f' g')
  = do
    b1 <- eqGExpSt s s'
    b2 <- eqGExpSt f f'
    b3 <- eqGExpSt g g'
    return $ b1 && b2 && b3
eqGExpSt (RetErr t) (RetErr t')
  = eqGExpSt t t'
eqGExpSt (BindErr t u) (BindErr t' u')
  = do
    b1 <- eqGExpSt t t'
    b2 <- eqGExpSt u u'
    return $ b1 && b2
eqGExpSt (Throw t) (Throw t')
  = eqGExpSt t t'
eqGExpSt (Catch t u) (Catch t' u')
  = do
    b1 <- eqGExpSt t t'
    b2 <- eqGExpSt u u'
    return $ b1 && b2
eqGExpSt (RetSt t) (RetSt t')
  = eqGExpSt t t'
eqGExpSt (BindSt t u) (BindSt t' u')
  = do
    b1 <- eqGExpSt t t'
    b2 <- eqGExpSt u u'
    return $ b1 && b2
eqGExpSt (Get t) (Get t')
  = eqGExpSt t t'
eqGExpSt (Put t) (Put t')
  = eqGExpSt t t'
eqGExpSt (Arr t u) (Arr t' u')
  = do
    b1 <- eqGExpSt t t'
    b2 <- eqGExpSt u u'
    return $ b1 && b2
eqGExpSt (ArrLen t) (ArrLen t')
  = eqGExpSt t t'
eqGExpSt (ArrIx t u) (ArrIx t' u')
  = do
    b1 <- eqGExpSt t t'
    b2 <- eqGExpSt u u'
    return $ b1 && b2
eqGExpSt (Let t u) (Let t' u')
  = do
    b1 <- eqGExpSt t t'
    b2 <- eqGExpSt u u'
    return $ b1 && b2
eqGExpSt (Save t) (Save t')
  = eqGExpSt t t'
eqGExpSt _ _
  = return False

eqGExp :: GExp c a -> GExp c b -> Bool
eqGExp e e' = evalState (eqGExpSt e e') 0

------------
-- Utilities
------------

mapTup :: (a -> c) -> (b -> d) -> (a , b) -> (c, d)
mapTup f g (x,y) = (f x, g y)

comp :: (c a, c b, c d)
  => GExp c (b -> d) -> GExp c (a -> b) -> GExp c (a -> d)
comp g f = Lam $ App g . App f

(*.) :: (c a, c b, c d)
  => GExp c (b -> d) -> GExp c (a -> b) -> GExp c (a -> d)
(*.) = undefined

rec :: (c a, c Int)
  => GExp c Int -> GExp c (Int -> a -> a) -> GExp c a -> GExp c a
rec n f m = Prim (Rec n f m)

seqSt :: (c a, c b, c s, c (State s b))
  => GExp c (State s a) -> GExp c (State s b) -> GExp c (State s b)
seqSt m m' = BindSt m (Lam $ const $ m')

unknown :: c a => String -> GExp c a
unknown = Var

unit :: GExp c ()
unit = Unit

lam :: (c a, c b) => (GExp c a -> GExp c b) -> GExp c (a -> b)
lam = Lam

app :: (c a, c b) => GExp c (a -> b) -> GExp c a -> GExp c b
app = App

(*$) :: (c a, c b) => GExp c (a -> b) -> GExp c a -> GExp c b
(*$) = app

lam2 :: (c a, c b, c d, c (b -> d))
  => (GExp c a -> GExp c b -> GExp c d) -> GExp c (a -> b -> d)
lam2 f = lam $ \ x -> (lam $ \ y -> f x y)

app2 :: (c a, c b, c d, c (b -> d))
  => GExp c (a -> b -> d) -> GExp c a -> GExp c b -> GExp c d
app2 f x y = app (app f x) y

instance Num (GExp c Int) where
  x + y       = Prim (Add x y)
  x * y       = Prim (Mul x y)
  abs         = undefined
  signum      = undefined
  fromInteger = Lift . fromIntegral
  negate    x = Prim (Mul (Lift (-1)) x)

type BoolE = Either () ()

pattern TrueE :: Either () b
pattern TrueE  = Left ()

pattern FalseE :: Either a ()
pattern FalseE = Right ()

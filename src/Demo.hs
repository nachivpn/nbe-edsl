{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RebindableSyntax #-}
module Demo where

import Prelude hiding (Monad(..))
import GExp
import NbE.OpenNbE hiding (power, cube, flipE, multipleOf3)
import Control.Monad.State.Lazy ( State )

type Rf        = Reifiable
type Rf2 a b   = (Rf a, Rf b)
type Rf3 a b c = (Rf2 a b, Rf c)

--
-- Power
--

-- rec n g x ~ g 1 (g 2 .... (g n x))

-- power n x = x^n
power :: Exp (Int -> Int -> Int)
power = lam2 (\n x -> rec n (f x) 1)
  where f x = lam2 $ \_ acc -> (x * acc)

-- _^3
cube :: Exp (Int -> Int)
cube = app power 3

-- 3^_
multipleOf3 :: Exp (Int -> Int)
multipleOf3 = app (flip' power) 3
    where flip' f = lam2 $ \ x y -> app2 f y x

---------
-- Arrays
---------

-- | Create a new array
newArr :: (Rf a)
    => Exp Int -> Exp (Int -> a) -> Exp (Arr a)
newArr = Arr

-- | Length of an array
lenArr :: (Rf a)
    => Exp (Arr a) -> Exp Int
lenArr = ArrLen

-- | Index into an array
(!) :: Rf a => Exp (Arr a) -> Exp Int -> Exp a
(!) = ArrIx

-- | Map over an array
mapArr :: (Rf a, Rf b) => Exp (a -> b) -> Exp (Arr a) -> Exp (Arr b)
mapArr f arr = newArr (lenArr arr) (f `comp` (lam $ (!) arr))

-- | Fold over an array
foldArr :: (Rf2 a b) => Exp (b -> a -> b) -> Exp b -> Exp (Arr a) -> Exp b
foldArr f base arr = rec
    (lenArr arr)
    (lam2 $ \ i acc -> app2 f acc (arr ! i))
    base

-- map +1, map +2
mapMap :: Exp (Arr Int -> Arr Int)
mapMap = lam $ \arr -> mapArr (lam (+2)) (mapArr (lam (+1)) arr)

-- map +2, fold into sum
mapFold :: Exp (Arr Int -> Int)
mapFold = lam (\arr -> foldArr go 0 (mapArr (lam (+2)) arr))
    where go = lam2 (\acc x -> acc + x)

prgBr :: Exp (Either Int Int -> Arr Int -> Arr Int)
prgBr = lam2 $ \ scr arr ->
    mapArr (lam (+1)) $ case' scr
        (lam $ \x -> mapArr (lam (+x)) arr)
        (lam $ \y -> arr)

--------
-- State
--------

put :: Rf s => Exp s -> Exp (State s ())
put = Put

returnSt :: Rf2 s a => Exp a -> Exp (State s a)
returnSt = RetSt

get :: Rf s => Exp (State s s)
get = Get (lam returnSt)

bindSt :: Rf3 s a b => Exp (State s a) -> Exp (a -> State s b) -> Exp (State s b)
bindSt = BindSt

-- | A version of monads where everything is nested inside a wrapper w
--
-- w is the wrapper
-- m is the monad
-- c is a constraint that is applied to all the inner values
class NestedMonad c w m | w m -> c where
  return :: c a => w a -> w (m a)
  (>>=) :: (c a, c b) => w (m a) -> (w a -> w (m b)) -> w (m b)
  (>>) :: (c a, c b) => w (m a) -> w (m b) -> w (m b)
  m >> m' = m >>= const m'

instance Reifiable s => NestedMonad Reifiable (GExp Reifiable) (State s) where
  return = returnSt
  m >>= f = bindSt m (lam f)
  -- (>>) = seqSt

prgSt :: Exp (Arr Int -> State (Arr Int) Int)
prgSt = lam $ \ arr -> do
    put (mapArr (lam (+2)) arr)
    put (mapArr (lam (+1)) arr)
    arr' <- get
    returnSt (arr' ! 0)

prgBrSt :: Exp (Either Int Int -> Arr Int -> State (Arr Int) Int)
prgBrSt = lam2 $ \scr arr -> do
    put (mapArr (lam (+1)) arr)
    case' scr
        (lam $ \x -> put (mapArr (lam (+x)) arr))
        (lam $ \y -> returnSt unit)
    arr' <- get
    return (arr' ! 0)

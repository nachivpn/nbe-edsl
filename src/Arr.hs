{-# LANGUAGE ConstraintKinds #-}
module Arr where

import GExp ( comp, rec, Arr, GExp(App, Arr, ArrLen, ArrIx, Lam) )

-- | Create a new array
newArr :: (c a)
    => GExp c Int -> GExp c (Int -> a) -> GExp c (Arr a)
newArr = Arr

-- | Length of an array
lenArr :: (c a)
    => GExp c (Arr a) -> GExp c Int
lenArr = ArrLen

-- | Index into an array
ixArr :: ()
  => GExp c (Arr a) -> GExp c Int -> GExp c a
ixArr = ArrIx

-- | Map over an array
mapArr :: (c a, c b, c Int)
  => GExp c (a -> b) -> GExp c (Arr a) -> GExp c (Arr b)
mapArr f arr = Arr (ArrLen arr) (f `comp` (Lam $ ArrIx arr))

-- | Fold over an array
foldArr :: (c a, c b, c Int, c (b -> b))
  => GExp c (b -> a -> b) -> GExp c b -> GExp c (Arr a) -> GExp c b
foldArr f b arr = rec (lenArr arr)
  (Lam $ \ i -> Lam $ \ acc -> App (App f acc) (ixArr arr i)) b

module Type.Data.Nat.Sets where

import Prelude

import Type.Data.Nat.Reps (type (:*), D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, NProxy(NProxy), NaN, d1, d2, d3, d4, d5, d6, d7, d8, d9)

class Nat n where
  toInt :: NProxy n -> Int

class Nat n <= Pos n

instance failNaN :: Fail "NaN is not a natural number." => Nat NaN where
  toInt _ = 0
instance natD0 :: Nat D0 where toInt _ = 0
instance natD1 :: Nat D1 where toInt _ = 1
instance natD2 :: Nat D2 where toInt _ = 2
instance natD3 :: Nat D3 where toInt _ = 3
instance natD4 :: Nat D4 where toInt _ = 4
instance natD5 :: Nat D5 where toInt _ = 5
instance natD6 :: Nat D6 where toInt _ = 6
instance natD7 :: Nat D7 where toInt _ = 7
instance natD8 :: Nat D8 where toInt _ = 8
instance natD9 :: Nat D9 where toInt _ = 9

instance posNatD0 :: Pos x => Nat (x :* D0) where toInt n = subLastDec n
instance posNatD1 :: Pos x => Nat (x :* D1) where toInt n = subLastDec n + 1
instance posNatD2 :: Pos x => Nat (x :* D2) where toInt n = subLastDec n + 2
instance posNatD3 :: Pos x => Nat (x :* D3) where toInt n = subLastDec n + 3
instance posNatD4 :: Pos x => Nat (x :* D4) where toInt n = subLastDec n + 4
instance posNatD5 :: Pos x => Nat (x :* D5) where toInt n = subLastDec n + 5
instance posNatD6 :: Pos x => Nat (x :* D6) where toInt n = subLastDec n + 6
instance posNatD7 :: Pos x => Nat (x :* D7) where toInt n = subLastDec n + 7
instance posNatD8 :: Pos x => Nat (x :* D8) where toInt n = subLastDec n + 8
instance posNatD9 :: Pos x => Nat (x :* D9) where toInt n = subLastDec n + 9


instance posD1 :: Pos D1
instance posD2 :: Pos D2
instance posD3 :: Pos D3
instance posD4 :: Pos D4
instance posD5 :: Pos D5
instance posD6 :: Pos D6
instance posD7 :: Pos D7
instance posD8 :: Pos D8
instance posD9 :: Pos D9

instance posPosD0 :: Pos x => Pos (x :* D0)
instance posPosD1 :: Pos x => Pos (x :* D1)
instance posPosD2 :: Pos x => Pos (x :* D2)
instance posPosD3 :: Pos x => Pos (x :* D3)
instance posPosD4 :: Pos x => Pos (x :* D4)
instance posPosD5 :: Pos x => Pos (x :* D5)
instance posPosD6 :: Pos x => Pos (x :* D6)
instance posPosD7 :: Pos x => Pos (x :* D7)
instance posPosD8 :: Pos x => Pos (x :* D8)
instance posPosD9 :: Pos x => Pos (x :* D9)

subLastDec :: forall x d. Nat (x :* d) => Nat x => NProxy (x :* d) -> Int
subLastDec = div10Dec >>> toInt >>> (10 * _)

div10Dec :: forall x d. Nat (x :* d) => NProxy (x :* d) -> NProxy x
div10Dec _ = NProxy

reifyInt :: forall r. Partial => Int -> (forall n. Nat n => NProxy n -> r) -> r
reifyInt i f
 | i == 0    = f (NProxy :: NProxy D0)
 | otherwise = reifyIntP i f

reifyIntP :: forall r. Partial => Int -> (forall n. Pos n => NProxy n -> r) -> r
reifyIntP i f
  | i == 1 = f d1
  | i == 2 = f d2
  | i == 3 = f d3
  | i == 4 = f d4
  | i == 5 = f d5
  | i == 6 = f d6
  | i == 7 = f d7
  | i == 8 = f d8
  | i == 9 = f d9
  | otherwise =
    let d = div i 10
        m = mod i 10
    in case m of
      0 -> reifyIntP d f0
      1 -> reifyIntP d f1
      2 -> reifyIntP d f2
      3 -> reifyIntP d f3
      4 -> reifyIntP d f4
      5 -> reifyIntP d f5
      6 -> reifyIntP d f6
      7 -> reifyIntP d f7
      8 -> reifyIntP d f8
      9 -> reifyIntP d f9
    where f0 :: forall e. Pos e => NProxy e -> r
          f0 _ = f (NProxy :: NProxy (e :* D0))
          f1 :: forall e. Pos e => NProxy e -> r
          f1 _ = f (NProxy :: NProxy (e :* D1))
          f2 :: forall e. Pos e => NProxy e -> r
          f2 _ = f (NProxy :: NProxy (e :* D2))
          f3 :: forall e. Pos e => NProxy e -> r
          f3 _ = f (NProxy :: NProxy (e :* D3))
          f4 :: forall e. Pos e => NProxy e -> r
          f4 _ = f (NProxy :: NProxy (e :* D4))
          f5 :: forall e. Pos e => NProxy e -> r
          f5 _ = f (NProxy :: NProxy (e :* D5))
          f6 :: forall e. Pos e => NProxy e -> r
          f6 _ = f (NProxy :: NProxy (e :* D6))
          f7 :: forall e. Pos e => NProxy e -> r
          f7 _ = f (NProxy :: NProxy (e :* D7))
          f8 :: forall e. Pos e => NProxy e -> r
          f8 _ = f (NProxy :: NProxy (e :* D8))
          f9 :: forall e. Pos e => NProxy e -> r
          f9 _ = f (NProxy :: NProxy (e :* D9))

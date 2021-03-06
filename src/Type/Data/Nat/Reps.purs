module Type.Data.Nat.Reps
  ( kind Nat, NProxy(NProxy), NCons, type (:*)
  , D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, NaN
  , d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, nan
  ) where

import Prelude

foreign import kind Nat

foreign import data D0 :: Nat
foreign import data D1 :: Nat
foreign import data D2 :: Nat
foreign import data D3 :: Nat
foreign import data D4 :: Nat
foreign import data D5 :: Nat
foreign import data D6 :: Nat
foreign import data D7 :: Nat
foreign import data D8 :: Nat
foreign import data D9 :: Nat

foreign import data NaN :: Nat

data NProxy (n :: Nat) = NProxy

derive instance eqNProxy :: Eq (NProxy a)
 
derive instance ordNProxy :: Ord (NProxy a)
 
instance booleanAlgebraNProxy :: BooleanAlgebra (NProxy a)
 
instance boundedNProxy :: Bounded (NProxy a) where
  bottom = NProxy
  top = NProxy
 
instance commutativeRingNProxy :: CommutativeRing (NProxy a)
 
instance discardNProxy :: Discard (NProxy a) where
  discard = bind
 
instance heytingAlgebraNProxy :: HeytingAlgebra (NProxy a) where
  conj _ _ = NProxy
  disj _ _ = NProxy
  implies _ _ = NProxy
  ff = NProxy
  not _ = NProxy
  tt = NProxy
 
instance ringNProxy :: Ring (NProxy a) where
  sub _ _ = NProxy
 
instance semigroupNProxy :: Semigroup (NProxy a) where
  append _ _ = NProxy
 
instance semiringNProxy :: Semiring (NProxy a) where
  add _ _ = NProxy
  mul _ _ = NProxy
  one = NProxy
  zero = NProxy
 
instance showNProxy :: Show (NProxy a) where
  show _ = "NProxy"

foreign import data NCons :: Nat -> Nat -> Nat
infixl 6 type NCons as :*

d0 :: NProxy D0
d0 = NProxy
d1 :: NProxy D1
d1 = NProxy
d2 :: NProxy D2
d2 = NProxy
d3 :: NProxy D3
d3 = NProxy
d4 :: NProxy D4
d4 = NProxy
d5 :: NProxy D5
d5 = NProxy
d6 :: NProxy D6
d6 = NProxy
d7 :: NProxy D7
d7 = NProxy
d8 :: NProxy D8
d8 = NProxy
d9 :: NProxy D9
d9 = NProxy

nan :: NProxy NaN
nan = NProxy

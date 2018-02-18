module Type.Data.Nat.Ops where

import Prelude hiding (class Eq, add, sub, mul, eq, (==))

import Data.Tuple (Tuple(Tuple))
import Type.Data.Boolean (kind Boolean, True, False)
import Type.Data.Nat.Reps (type (:*), D0, D1, D2, D3, D4, D5, D6, D7, D8, D9, NProxy(..), NaN, kind Nat)
import Type.Data.Nat.Sets (class Nat, class Pos)
import Type.Data.Ordering (kind Ordering, OProxy(OProxy), LT, GT, EQ)

-- Successor and predecessor

class Pos y <= Succ (x :: Nat) y | x -> y, y -> x

instance succNat
  :: (Pos y, IsZero y yz,
      DivMod10 x xi xl, SuccP xi xl yi yl yz, DivMod10 y yi yl)
  => Succ x y

class SuccP (xh :: Nat) (xl :: Nat) (yh :: Nat) (yl :: Nat) (yz :: Boolean)
  | xh xl -> yh yl yz, yh yl yz -> xh xl

instance failPredZero
  :: Fail "Cannot produce predecessor of D0"
  => SuccP NaN NaN D0 D0 True
instance succPxiD0xiD1 :: Nat xi => SuccP xi D0 xi D1 False
instance succPxiD1xiD2 :: Nat xi => SuccP xi D1 xi D2 False
instance succPxiD2xiD3 :: Nat xi => SuccP xi D2 xi D3 False
instance succPxiD3xiD4 :: Nat xi => SuccP xi D3 xi D4 False
instance succPxiD4xiD5 :: Nat xi => SuccP xi D4 xi D5 False
instance succPxiD5xiD6 :: Nat xi => SuccP xi D5 xi D6 False
instance succPxiD6xiD7 :: Nat xi => SuccP xi D6 xi D7 False
instance succPxiD7xiD8 :: Nat xi => SuccP xi D7 xi D8 False
instance succPxiD8xiD9 :: Nat xi => SuccP xi D8 xi D9 False
instance succPxiD9iyD0 :: (Nat xi, Succ xi yi) => SuccP xi D9 yi D0 False

succ :: forall x y. Succ x y => NProxy x -> NProxy y
succ _ = NProxy

class Pos x <= Pred x (y :: Nat) | x -> y, y -> x
instance succPred :: Succ x y => Pred y x

pred :: forall x y. Pred x y => NProxy x -> NProxy y
pred _ = NProxy

-- Addition and Subtraction

class Nat x <= AddP x (y :: Nat) (z :: Nat) | x y -> z, z x -> y
instance addPD0ToNat  :: Nat y => AddP D0 y y
instance addPD1ToSucc :: Succ y z => AddP D1 y z
instance addPD2ToSucc :: (Succ z z', AddP D1 y z) => AddP D2 y z'
instance addPD3ToSucc :: (Succ z z', AddP D2 y z) => AddP D3 y z'
instance addPD4ToSucc :: (Succ z z', AddP D3 y z) => AddP D4 y z'
instance addPD5ToSucc :: (Succ z z', AddP D4 y z) => AddP D5 y z'
instance addPD6ToSucc :: (Succ z z', AddP D5 y z) => AddP D6 y z'
instance addPD7ToSucc :: (Succ z z', AddP D6 y z) => AddP D7 y z'
instance addPD8ToSucc :: (Succ z z', AddP D7 y z) => AddP D8 y z'
instance addPD9ToSucc :: (Succ z z', AddP D8 y z) => AddP D9 y z'
instance addPMultiDigits
  :: ( Pos (xi :* xl), Nat z, AddP xi yi zi, DivMod10 y yi yl
     , AddP xl (zi :* yl) z)
  => AddP (xi :* xl) y z

class (AddP x y z, AddP y x z) <= Add x y z | x y -> z, z x -> y, z y -> x
instance addTypeLevelRelation :: (AddP x y z, AddP y x z) => Add x y z

add :: forall x y z. (Add x y z) => NProxy x -> NProxy y -> NProxy z
add _ _ = NProxy
infixl 6 add as +

class Sub (x :: Nat) (y :: Nat) (z :: Nat) | x y -> z, z x -> y, z y -> x
instance subtractTypeLevelRelation :: Add x y z => Sub z y x

sub :: forall x y z. Sub x y z => NProxy x -> NProxy y -> NProxy z
sub _ _ = NProxy
infixl 6 sub as -

-- Multiplication

class (Nat x, Nat y) <= Mul x y (z :: Nat) | x y -> z
instance mulD0Nat :: Nat y => Mul D0 y D0
instance mulD1Nat :: Nat y => Mul D1 y y
instance mulD2Nat :: Add y y z => Mul D2 y z
instance mulD3Nat :: (Add z y z', Mul D2 y z) => Mul D3 y z'
instance mulD4Nat :: (Add z y z', Mul D3 y z) => Mul D4 y z'
instance mulD5Nat :: (Add z y z', Mul D4 y z) => Mul D5 y z'
instance mulD6Nat :: (Add z y z', Mul D5 y z) => Mul D6 y z'
instance mulD7Nat :: (Add z y z', Mul D6 y z) => Mul D7 y z'
instance mulD8Nat :: (Add z y z', Mul D7 y z) => Mul D8 y z'
instance mulD9Nat :: (Add z y z', Mul D8 y z) => Mul D9 y z'
instance mulMultidigits
  :: (Pos (xi :* xl), Mul xi y z, Mul10 z z10, Mul xl y dy, Add dy z10 z')
  => Mul (xi :* xl) y z'

mul :: forall x y z. Mul x y z => NProxy x -> NProxy y -> NProxy z
mul _ _ = NProxy
infixl 7 mul as *

-- Division

class (Nat x, Pos y)
  <= DivMod (x :: Nat) (y :: Nat) (q :: Nat) (r :: Nat)
  | x y -> q r

instance divModNatPos
  :: (Nat x, Pos y, Trich x y cmp, DivModP x y q r cmp)
  => DivMod x y q r

class (Nat x, Pos y) <=
  DivModP (x :: Nat) (y :: Nat) (q :: Nat) (r :: Nat) (cmp :: Ordering)
  | x y cmp -> q r, q r cmp y -> x, q r cmp x -> y

instance divModPD0Nat :: (Nat x, Pos y) => DivModP x y D0 x LT
instance divModPD0D1 :: (Nat x, Pos y) => DivModP x y D1 D0 EQ
instance divModPQR
  :: (Nat x, Pos y, Sub x y x', Pred q q', DivMod x' y q' r)
  => DivModP x y q r GT

divMod
  :: forall x y q r
   . DivMod x y q r
  => NProxy x -> NProxy y -> Tuple (NProxy q) (NProxy r)
divMod _ _ = Tuple NProxy NProxy

class Div (x :: Nat) (y :: Nat) (z :: Nat) | x y -> z, x z -> y, y z -> x
instance divNatPos :: (DivMod x y q r) => Div x y q

div :: forall x y z. Div x y z => NProxy x -> NProxy y -> NProxy z
div _ _ = NProxy

class Mod (x :: Nat) (y :: Nat) (r :: Nat) | x y -> r
instance modNatPos :: DivMod x y q r => Mod x y r

mod :: forall x y r. Mod x y r => NProxy x -> NProxy y -> NProxy r
mod _ _ = NProxy

-- Special cases

class Nat q <= Mul10 (x :: Nat) q | x -> q, q -> x
instance mul10Nat :: DivMod10 x q D0 => Mul10 q x

mul10 :: forall x q. Mul10 x q => NProxy x -> NProxy q
mul10 _ = NProxy

-- switching order of q and x in the entailment causes a bug!
class (Nat q, Nat x) <= DivMod10 x q (r :: Nat) | q r -> x, x -> q r

instance divMod10D0D0 :: DivMod10 D0 D0 D0
instance divMod10D1D0 :: DivMod10 D1 D0 D1
instance divMod10D2D0 :: DivMod10 D2 D0 D2
instance divMod10D3D0 :: DivMod10 D3 D0 D3
instance divMod10D4D0 :: DivMod10 D4 D0 D4
instance divMod10D5D0 :: DivMod10 D5 D0 D5
instance divMod10D6D0 :: DivMod10 D6 D0 D6
instance divMod10D7D0 :: DivMod10 D7 D0 D7
instance divMod10D8D0 :: DivMod10 D8 D0 D8
instance divMod10D9D0 :: DivMod10 D9 D0 D9
instance divMod10D1x :: (Nat (D1 :* l)) => DivMod10 (D1 :* l) D1 l
instance divMod10D2x :: (Nat (D2 :* l)) => DivMod10 (D2 :* l) D2 l
instance divMod10D3x :: (Nat (D3 :* l)) => DivMod10 (D3 :* l) D3 l
instance divMod10D4x :: (Nat (D4 :* l)) => DivMod10 (D4 :* l) D4 l
instance divMod10D5x :: (Nat (D5 :* l)) => DivMod10 (D5 :* l) D5 l
instance divMod10D6x :: (Nat (D6 :* l)) => DivMod10 (D6 :* l) D6 l
instance divMod10D7x :: (Nat (D7 :* l)) => DivMod10 (D7 :* l) D7 l
instance divMod10D8x :: (Nat (D8 :* l)) => DivMod10 (D8 :* l) D8 l
instance divMod10D9x :: (Nat (D9 :* l)) => DivMod10 (D9 :* l) D9 l
instance divModBeyond
  :: (Nat (x :* l), Nat ((x :* l) :* l'))
  => DivMod10 ((x :* l) :* l') (x :* l) l'

divMod10
  :: forall x q r
   . DivMod10 x q r
  => NProxy x -> Tuple (NProxy q) (NProxy r)
divMod10 _ = Tuple NProxy NProxy

class Nat x <= Div10 x (q :: Nat) | x -> q, q -> x
instance div10Nat :: DivMod10 x q r => Div10 x q

div10 :: forall x q. Div10 x q => NProxy x -> NProxy q
div10 _ = NProxy

class Pos d <= IsDivBy d (x :: Nat)
instance isDivByPosNat :: DivMod x d q D0 => IsDivBy d x

isDivBy :: forall d x. IsDivBy d x => NProxy d -> NProxy x
isDivBy _ = NProxy

-- Comparison

class Trich (x :: Nat) (y :: Nat) (o :: Ordering) | x y -> o

instance trichD0D0 :: Trich D0 D0 EQ
instance trichD0D1 :: Trich D0 D1 LT
instance trichD0D2 :: Trich D0 D2 LT
instance trichD0D3 :: Trich D0 D3 LT
instance trichD0D4 :: Trich D0 D4 LT
instance trichD0D5 :: Trich D0 D5 LT
instance trichD0D6 :: Trich D0 D6 LT
instance trichD0D7 :: Trich D0 D7 LT
instance trichD0D8 :: Trich D0 D8 LT
instance trichD0D9 :: Trich D0 D9 LT
instance trichD0Dxx :: Pos (yi :* yl) => Trich D0 (yi :* yl) LT
instance trichDxxD0 :: Pos (yi :* yl) => Trich (yi :* yl) D0 GT

instance trichD1D0 :: Trich D1 D0 GT
instance trichD1D1 :: Trich D1 D1 EQ
instance trichD1D2 :: Trich D1 D2 LT
instance trichD1D3 :: Trich D1 D3 LT
instance trichD1D4 :: Trich D1 D4 LT
instance trichD1D5 :: Trich D1 D5 LT
instance trichD1D6 :: Trich D1 D6 LT
instance trichD1D7 :: Trich D1 D7 LT
instance trichD1D8 :: Trich D1 D8 LT
instance trichD1D9 :: Trich D1 D9 LT
instance trichD1Dxx :: Pos (yi :* yl) => Trich D1 (yi :* yl) LT
instance trichDxxD1 :: Pos (yi :* yl) => Trich (yi :* yl) D1 GT

instance trichD2D0 :: Trich D2 D0 GT
instance trichD2D1 :: Trich D2 D1 GT
instance trichD2D2 :: Trich D2 D2 EQ
instance trichD2D3 :: Trich D2 D3 LT
instance trichD2D4 :: Trich D2 D4 LT
instance trichD2D5 :: Trich D2 D5 LT
instance trichD2D6 :: Trich D2 D6 LT
instance trichD2D7 :: Trich D2 D7 LT
instance trichD2D8 :: Trich D2 D8 LT
instance trichD2D9 :: Trich D2 D9 LT
instance trichD2Dxx :: Pos (yi :* yl) => Trich D2 (yi :* yl) LT
instance trichDxxD2 :: Pos (yi :* yl) => Trich (yi :* yl) D2 GT

instance trichD3D0 :: Trich D3 D0 GT
instance trichD3D1 :: Trich D3 D1 GT
instance trichD3D2 :: Trich D3 D2 GT
instance trichD3D3 :: Trich D3 D3 EQ
instance trichD3D4 :: Trich D3 D4 LT
instance trichD3D5 :: Trich D3 D5 LT
instance trichD3D6 :: Trich D3 D6 LT
instance trichD3D7 :: Trich D3 D7 LT
instance trichD3D8 :: Trich D3 D8 LT
instance trichD3D9 :: Trich D3 D9 LT
instance trichD3Dxx :: Pos (yi :* yl) => Trich D3 (yi :* yl) LT
instance trichDxxD3 :: Pos (yi :* yl) => Trich (yi :* yl) D3 GT

instance trichD4D0 :: Trich D4 D0 GT
instance trichD4D1 :: Trich D4 D1 GT
instance trichD4D2 :: Trich D4 D2 GT
instance trichD4D3 :: Trich D4 D3 GT
instance trichD4D4 :: Trich D4 D4 EQ
instance trichD4D5 :: Trich D4 D5 LT
instance trichD4D6 :: Trich D4 D6 LT
instance trichD4D7 :: Trich D4 D7 LT
instance trichD4D8 :: Trich D4 D8 LT
instance trichD4D9 :: Trich D4 D9 LT
instance trichD4Dxx :: Pos (yi :* yl) => Trich D4 (yi :* yl) LT
instance trichDxxD4 :: Pos (yi :* yl) => Trich (yi :* yl) D4 GT

instance trichD5D0 :: Trich D5 D0 GT
instance trichD5D1 :: Trich D5 D1 GT
instance trichD5D2 :: Trich D5 D2 GT
instance trichD5D3 :: Trich D5 D3 GT
instance trichD5D4 :: Trich D5 D4 GT
instance trichD5D5 :: Trich D5 D5 EQ
instance trichD5D6 :: Trich D5 D6 LT
instance trichD5D7 :: Trich D5 D7 LT
instance trichD5D8 :: Trich D5 D8 LT
instance trichD5D9 :: Trich D5 D9 LT
instance trichD5Dxx :: Pos (yi :* yl) => Trich D5 (yi :* yl) LT
instance trichDxxD5 :: Pos (yi :* yl) => Trich (yi :* yl) D5 GT

instance trichD6D0 :: Trich D6 D0 GT
instance trichD6D1 :: Trich D6 D1 GT
instance trichD6D2 :: Trich D6 D2 GT
instance trichD6D3 :: Trich D6 D3 GT
instance trichD6D4 :: Trich D6 D4 GT
instance trichD6D5 :: Trich D6 D5 GT
instance trichD6D6 :: Trich D6 D6 EQ
instance trichD6D7 :: Trich D6 D7 LT
instance trichD6D8 :: Trich D6 D8 LT
instance trichD6D9 :: Trich D6 D9 LT
instance trichD6Dxx :: Pos (yi :* yl) => Trich D6 (yi :* yl) LT
instance trichDxxD6 :: Pos (yi :* yl) => Trich (yi :* yl) D6 GT

instance trichD7D0 :: Trich D7 D0 GT
instance trichD7D1 :: Trich D7 D1 GT
instance trichD7D2 :: Trich D7 D2 GT
instance trichD7D3 :: Trich D7 D3 GT
instance trichD7D4 :: Trich D7 D4 GT
instance trichD7D5 :: Trich D7 D5 GT
instance trichD7D6 :: Trich D7 D6 GT
instance trichD7D7 :: Trich D7 D7 EQ
instance trichD7D8 :: Trich D7 D8 LT
instance trichD7D9 :: Trich D7 D9 LT
instance trichD7Dxx :: Pos (yi :* yl) => Trich D7 (yi :* yl) LT
instance trichDxxD7 :: Pos (yi :* yl) => Trich (yi :* yl) D7 GT

instance trichD8D0 :: Trich D8 D0 GT
instance trichD8D1 :: Trich D8 D1 GT
instance trichD8D2 :: Trich D8 D2 GT
instance trichD8D3 :: Trich D8 D3 GT
instance trichD8D4 :: Trich D8 D4 GT
instance trichD8D5 :: Trich D8 D5 GT
instance trichD8D6 :: Trich D8 D6 GT
instance trichD8D7 :: Trich D8 D7 GT
instance trichD8D8 :: Trich D8 D8 EQ
instance trichD8D9 :: Trich D8 D9 LT
instance trichD8Dxx :: Pos (yi :* yl) => Trich D8 (yi :* yl) LT
instance trichDxxD8 :: Pos (yi :* yl) => Trich (yi :* yl) D8 GT

instance trichD9D0 :: Trich D9 D0 GT
instance trichD9D1 :: Trich D9 D1 GT
instance trichD9D2 :: Trich D9 D2 GT
instance trichD9D3 :: Trich D9 D3 GT
instance trichD9D4 :: Trich D9 D4 GT
instance trichD9D5 :: Trich D9 D5 GT
instance trichD9D6 :: Trich D9 D6 GT
instance trichD9D7 :: Trich D9 D7 GT
instance trichD9D8 :: Trich D9 D8 GT
instance trichD9D9 :: Trich D9 D9 EQ
instance trichD9Dxx :: Pos (yi :* yl) => Trich D9 (yi :* yl) LT
instance trichDxxD9 :: Pos (yi :* yl) => Trich (yi :* yl) D9 GT

instance trichDxxDxx :: (Pos (xi :* xl), Pos (yi :* yl), Trich xl yl rl, Trich xi yi ri, CS ri rl r) => Trich (xi :* xl) (yi :* yl) r

trich :: forall x y o. Trich x y o => NProxy x -> NProxy y -> OProxy o
trich _ _ = OProxy

class CS (r1 :: Ordering) (r2 :: Ordering) (r3 :: Ordering) | r1 r2 -> r3
instance csEQrr :: CS EQ r r
instance csGTrGT :: CS GT r GT
instance csLTrLT :: CS LT r LT

class Eq (x :: Nat) (y :: Nat)
instance trichEq :: Trich x y EQ => Eq x y

eq :: forall x y. Eq x y => NProxy x -> NProxy y -> Unit
eq _ _ = unit

class Gt (x :: Nat) (y :: Nat)
instance trichGt :: (Trich x y GT) => Gt x y

gt :: forall x y. Gt x y => NProxy x -> NProxy y -> Unit
gt _ _ = unit

class Lt (x :: Nat) (y :: Nat)
instance trichLt :: (Trich x y LT) => Lt x y

lt :: forall x y. Lt x y => NProxy x -> NProxy y -> Unit
lt _ _ = unit

class GtEq (x :: Nat) (y :: Nat)
instance trichGtEq :: (Succ x x', Trich x' y GT) => GtEq x y

gteq :: forall x y. GtEq x y => NProxy x -> NProxy y -> Unit
gteq _ _ = unit

class LtEq (x :: Nat) (y :: Nat)
instance trichLtEq :: (Succ y y', Trich x y' LT) => LtEq x y

lteq :: forall x y. LtEq x y => NProxy x -> NProxy y -> Unit
lteq _ _ = unit

infixl 4 eq as ==
infixl 4 gt as >
infixl 4 lt as <
infixl 4 gteq as >=
infixl 4 lteq as <=

class MaxP (x :: Nat) (y :: Nat) (b :: Ordering) (r :: Nat) | x y b -> r
instance maxPLT :: MaxP x y LT y
instance maxPEQ :: MaxP x y EQ y
instance maxPGT :: MaxP x y GT x

class Max (x :: Nat) (y :: Nat) (z :: Nat) | x y -> z
instance maxRelation :: (MaxP x y b z, Trich x y b) => Max x y z

max :: forall x y z. Max x y z => NProxy x -> NProxy y -> NProxy z
max _ _ = NProxy

class Min (x :: Nat) (y :: Nat) (z :: Nat) | x y -> z
instance minRelation :: (MaxP y x b z, Trich x y b) => Min x y z

min :: forall x y z. Min x y z => NProxy x -> NProxy y -> NProxy z
min _ _ = NProxy

class (Nat x, Nat y, Nat gcd) <= GCD x y gcd | x y -> gcd
instance gcdRelation
  :: (Nat x, Nat y, Trich x y cmp, IsZero y yz, GCDP x y yz cmp gcd)
  => GCD x y gcd

class (Nat x, Nat y, Nat gcd) <= GCDP x y (yz :: Boolean) (cmp :: Ordering) gcd
  | x y yz cmp -> gcd
instance gcdpD0 :: Nat x => GCDP x D0 True cmp D0
instance gcdpXYLT :: (Nat x, Nat y, GCD y x gcd) => GCDP x y False LT gcd
instance gcdpXX :: Nat x => GCDP x x False EQ x
instance gcdpXYGT :: (Nat x, Nat y, Sub x y x', GCD x' y gcd) => GCDP x y False GT gcd

gcd :: forall x y z. GCD x y z => NProxy x -> NProxy y -> NProxy z
gcd _ _ = NProxy

-- Internal

class IsZero (x :: Nat) (r :: Boolean) | x -> r
instance isZeroD0 :: IsZero D0 True
instance isZeroD1 :: IsZero D1 False
instance isZeroD2 :: IsZero D2 False
instance isZeroD3 :: IsZero D3 False
instance isZeroD4 :: IsZero D4 False
instance isZeroD5 :: IsZero D5 False
instance isZeroD6 :: IsZero D6 False
instance isZeroD7 :: IsZero D7 False
instance isZeroD8 :: IsZero D8 False
instance isZeroD9 :: IsZero D9 False
instance isZeroPos :: Pos x => IsZero (x :* d) False

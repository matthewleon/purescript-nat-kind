module Test.Main where

import Prelude hiding (eq,add,sub,mul)

import Control.Monad.Aff.AVar (AVAR)
import Control.Monad.Aff.Console (CONSOLE)
import Control.Monad.Eff (Eff)
import Data.Tuple (Tuple(..))
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)
import Test.Unit.Console (TESTOUTPUT)
import Test.Unit.Main (runTest)
import Type.Data.Nat (type (:*), D2, D3, D4, NProxy(..), add, d0, d1, d2, d23, d24, d3, d4, d5, d6, d7, d8, d9, div10, divMod, divMod10, eq, gt, gteq, lt, lteq, mul, pred, sub, succ, toInt, trich)
import Type.Data.Ordering (OProxy(..), LT, GT, EQ)

d234 :: NProxy (D2 :* D3 :* D4)
d234 = NProxy

main :: forall e. Eff (console :: CONSOLE, testOutput :: TESTOUTPUT, avar :: AVAR | e) Unit
main = runTest tests

tests :: ∀ e. TestSuite e
tests = suite "base 10 nats" do
  suite "basic digits" do
    test "0" do
      equal 0 $ toInt d0
    test "1" do
      equal 1 $ toInt d1
    test "2" do
      equal 2 $ toInt d2
    test "3" do
      equal 3 $ toInt d3
    test "4" do
      equal 4 $ toInt d4
    test "5" do
      equal 5 $ toInt d5
    test "6" do
      equal 6 $ toInt d6
    test "7" do
      equal 7 $ toInt d7
    test "8" do
      equal 8 $ toInt d8
    test "9" do
      equal 9 $ toInt d9
  suite "succ" do
    test "succ 2" do
      equal 3 $ toInt $ succ d2
    test "succ 23" do
      equal 24 $ toInt $ succ d23
    test "succ 234" do
      equal 235 $ toInt $ succ d234
  suite "pred" do
    test "pred 2" do
      equal 1 $ toInt $ pred d2
    test "pred 23" do
      equal 22 $ toInt $ pred d23
    test "pred 234" do
      equal 233 $ toInt $ pred d234
    -- This one should fail type checking:
    -- equal 0 $ toInt $ pred d0
  suite "trich" do
    test "2 < 3" do
      equal (OProxy :: OProxy LT) $ trich d2 d3
    test "5 > 3" do
      equal (OProxy :: OProxy GT) $ trich d5 d3
    test "3 = 3" do
      equal (OProxy :: OProxy EQ) $ trich d3 d3
    test "2 < 23" do
      equal (OProxy :: OProxy LT) $ trich d2 d23
    test "23 > 2" do
      equal (OProxy :: OProxy GT) $ trich d23 d2
    test "23 = 23" do
      equal (OProxy :: OProxy EQ) $ trich d23 d23
    test "23 < 234" do
      equal (OProxy :: OProxy LT) $ trich d23 d234
    test "234 > 23" do
      equal (OProxy :: OProxy GT) $ trich d234 d23
  suite "comparisons" do
    test "0 < 5" do
      equal unit $ d0 `lt` d5
    test "0 <= 5" do
      equal unit $ d0 `lteq` d5
    test "5 > 0" do
      equal unit $ d5 `gt` d0
    test "5 >= 0" do
      equal unit $ d5 `gteq` d0
    test "0 = 0" do
      equal unit $ d0 `eq` d0
  suite "add" do
    test "2 + 3" do
      equal 5 $ toInt $ add d2 d3
    test "23 + 24" do
      equal 47 $ toInt $ add d23 d24
  suite "sub" do
    test "8 - 3" do
      equal 5 $ toInt $ sub d8 d3
    test "23 - 8" do
      equal 15 $ toInt $ sub d23 d8
    -- This one should fail type checking:
    -- equal 0 $ toInt $ sub d2 d3
  suite "mul" do
    test "2 * 3" do
      equal 6 $ toInt $ mul d2 d3
    test "3 * 23" do
      equal 69 $ toInt $ mul d3 d23
  suite "divMod" do
    test "5 / 2" do
      case d5 `divMod` d2 of
        (Tuple a b) → equal (Tuple 2 1) (Tuple (toInt a) (toInt b))
    test "8 / 3" do
      case d8 `divMod` d3 of
        (Tuple a b) → equal (Tuple 2 2) (Tuple (toInt a) (toInt b))
    test "23 / 3" do
      case d23 `divMod` d3 of
        (Tuple a b) → equal (Tuple 7 2) (Tuple (toInt a) (toInt b))
    -- dividing large numbers type checks VERY SLOWLY, uncomment these tests
    -- only if you're very serious about testing divMod!
    -- test "234 / 3" do
    --   case d234 `divMod` d3 of
    --     (Tuple a b) → equal (Tuple 78 0) (Tuple (toInt a) (toInt b))
    -- test "234 / 2" do
    --   case d234 `divMod` d2 of
    --     (Tuple a b) → equal (Tuple 78 0) (Tuple (toInt a) (toInt b))
  suite "divMod10" do
    test "8 / 10" do
      case divMod10 d8 of
        (Tuple a b) → equal (Tuple 0 8) (Tuple (toInt a) (toInt b))
    test "23 / 10" do
      case divMod10 d23 of
        (Tuple a b) → equal (Tuple 2 3) (Tuple (toInt a) (toInt b))
    test "234 / 10" do
      case divMod10 d234 of
        (Tuple a b) → equal (Tuple 23 4) (Tuple (toInt a) (toInt b))
  suite "div10" do
    test "234 / 10" do
      equal 23 $ toInt $ div10 d234
    test "23 / 10" do
      equal 2 $ toInt $ div10 d23
    test "5 / 10" do
      equal 0 $ toInt $ div10 d5

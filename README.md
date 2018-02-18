# purescript-nat-kind

Type level natural numbers.

This package is a fork of `purescript-typelevel` by Bodil Stokke. It is updated to use the tools provided by `purescript-typelevel-prelude`, and to provide a Proxy type, `NProxy`. There are other small tweaks.

`purescript-typelevel`, in turn, is a direct port of the Haskell [type-level](https://github.com/forsyde/type-level) package by Acosta, Kiselyov, Jeltsch et al.

## Type Level Numbers

This package provides a way to represent type level natural numbers and booleans, with a useful set of operations for both.

A natural number is expressed at the type level using uninhabited types with a `D` prefixed to the number: `D0`, `D1`, `D2` etc. You can use the `:*` type operator to combine digits: eg. `D1 :* D3 :* D3 :* D7` makes the number 1337. Aliases are provided for two digit numbers: `D10`, `D11` etc. up to `D99`. Values of each type are also provided, with the lower case prefix `d`, so: `d0`, `d1`, `d2` etc. up to `d99`.

Two type classes are provided acting as sets: `Nat` is the set of natural numbers (zero to infinity), and `Pos` is the set of positive numbers (1 to infinity). `Nat` defines the function `toInt`, which converts type level numbers to the value level. To move integer values to the type level, use the `reifyInt` function.

You can express arithmetic operators as type class constraints on type level numbers. For instance, to express that a type `c` is the sum of types `a` and `b`, you would use the type signature `∀ a b c. (Nat a, Nat b, Add a b c) ⇒ a → b → c`. To express that a type `a` must be less than another type `b`, you would use the type signature `∀ a b. (Nat a, Nat b, Lt a b) ⇒ a → b`.

Most of these constraints are fully relational, so that (even though a `Sub` constraint exists) you could make `c` the result of subtracting `b` from `a` by saying `∀ a b c. (Add c b a) ⇒ a → b → c`.

Note that while most of the arithmetic operations are reasonably performant, division (`DivMod` and friends) is not: division with a three digit divisor takes more than five minutes to type check on my machine.

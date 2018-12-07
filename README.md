Bidirectional Programming with Monadic Profunctors
==================================================

This package provides tools to work with *monadic profunctors*:
types that are both monads and profunctors.

Applications
------------

Currently known instances of monadic profunctors are certain types of
bidirectional programs, i.e., programs that have "invertible" interpretations.

- `attoparsec` (parsing) wrapper: [`unparse-attoparsec`](https://github.com/Lysxia/unparse-attoparsec)
- `QuickCheck` (random generation) wrapper: [`gap`](https://github.com/Lysxia/gap)
- `lens` wrapper: [`lens-monad`](https://github.com/Lysxia/lens-monad)

See also
--------

- [`codec`](https://hackage.haskell.org/package/codec) for a general
  monadic profunctor for bidirectional programming, has implementations for
  `aeson` and `binary`. The idea of monadic profunctors first came from this
  package.

### More bidirectional programming in Haskell

- [`lens`](https://hackage.haskell.org/package/lens)
- [`boomerang`](https://hackage.haskell.org/package/boomerang)
- [`roundtrip`](https://hackage.haskell.org/package/roundtrip)

### Generic programming with monoidal profunctors

- [`product-profunctors`](https://hackage.haskell.org/package/product-profunctors)
- [`one-liner`](https://hackage.haskell.org/package/one-liner)

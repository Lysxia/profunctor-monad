{- |
  Reexports important type classes from
  <https://hackage.haskell.org/package/base base>,
  <https://hackage.haskell.org/package/constraints constraints>,
  <https://hackage.haskell.org/package/profunctors profunctors>.
 -}

{-# LANGUAGE ConstraintKinds #-}

module Profunctor.Monad.Core
  ( -- * Constraint synonyms
    Functor1
  , Applicative1
  , Monad1
  , Alternative1

  -- * 

  , Functor
  , Applicative
  , Monad
  , Alternative

  -- * Constraints

  , ForallF
  , instF
  , (:-) (..)
  , Dict (..)
  ) where

import Control.Applicative

import Data.Constraint
import Data.Constraint.Forall

-- | Constraint equivalent to
--
-- > forall a. Functor (p a)
type Functor1 p = ForallF Functor p

-- | Constraint equivalent to
--
-- > forall a. Applicative (p a)
--
-- The quantified super-class instance is
-- explicitly added, since the type system currently can not deduce it.
type Applicative1 p = (Functor1 p, ForallF Applicative p)

-- | Constraint equivalent to
--
-- > forall a. Monad (p a)
--
-- The quantified super-class instance is
-- explicitly added, since the type system currently can not deduce it.
type Monad1 p = (Applicative1 p, ForallF Monad p)

-- | Constraint equivalent to
--
-- > forall a. Alternative (p a)
--
-- The quantified super-class instance is
-- explicitly added, since the type system currently can not deduce it.
type Alternative1 p = (Applicative1 p, ForallF Alternative p)

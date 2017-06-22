{- |
  Reexports important type classes from
  <https://hackage.haskell.org/package/base base>,
  <https://hackage.haskell.org/package/constraints constraints>.
 -}

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Profunctor.Monad.Core
  (
  -- * Constraint synonyms

  -- | The quantified super-class instances are explicitly added, since the type
  -- system can not deduce them.

    Functor1
  , Applicative1
  , Monad1
  , Alternative1
  , MonadPlus1

  -- * Standard type classes

  , Functor
  , Applicative
  , Monad
  , Alternative
  , MonadPlus

  -- * Constraints

  , ForallF
  , instF
  , (:-) (..)
  , Dict (..)
  ) where

import Control.Applicative
import Control.Monad

import Data.Constraint
import Data.Constraint.Forall

-- | Constraint equivalent to
--
-- > forall a. Functor (p a)
type Functor1 p = ForallF Functor p

-- | Constraint equivalent to
--
-- > forall a. Applicative (p a)
type Applicative1 p = (Functor1 p, ForallF Applicative p)

-- | Constraint equivalent to
--
-- > forall a. Monad (p a)
type Monad1 p = (Applicative1 p, ForallF Monad p)

-- | Constraint equivalent to
--
-- > forall a. Alternative (p a)
type Alternative1 p = (Applicative1 p, ForallF Alternative p)

-- | Constraint equivalent to
--
-- > forall a. MonadPlus (p a)
type MonadPlus1 p = (Monad1 p, Alternative1 p, ForallF MonadPlus p)

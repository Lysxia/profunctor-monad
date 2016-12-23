{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Profunctor.Monad.Contravariant
  ( Contravariant (..)
  , (=.)
  , (=:)
  ) where

import Control.Arrow (Kleisli(..), Arrow(arr))
import Control.Category (Category, (>>>))

infixl 5 =:, =.

-- | Types @p :: * -> * -> *@ which are contravariant functors
-- over their first parameter.
--
-- @
-- (f >>> g) `lmap` p
-- =
-- f `lmap` (g `lmap` p)
-- @
class Category (First p) => Contravariant p where
  type First p :: * -> * -> *
  lmap :: First p y x -> p x a -> p y a

instance Contravariant (->) where
  type First (->) = (->)
  lmap f g = g . f

instance Monad m => Contravariant (Kleisli m) where
  type First (Kleisli m) = Kleisli m
  lmap = (>>>)

-- | Mapping with a regular function.
(=.)
  :: (Contravariant p, Arrow (First p))
  => (y -> x) -> p x a -> p y a
(=.) = lmap . arr

-- | Monadic mapping; e.g., mapping which can fail ('Maybe').
(=:)
  :: (Contravariant p, First p ~ Kleisli m)
  => (y -> m x) -> p x a -> p y a
(=:) = lmap . Kleisli

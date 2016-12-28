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
-- Functor law:
--
-- @
-- lmap (i >>> j) p
-- =
-- lmap i (lmap j p)
-- @
--
-- If for every type @a@, @p a@ is an instance of 'Functor' (i.e., @p@ is a
-- covariant functor over its second parameter in Hask),
-- then 'lmap' should commute with 'fmap' (thus @p@ is a bifunctor):
--
-- @
-- lmap i (fmap f p)
-- =
-- fmap f (lmap i p)
-- @
--
-- If the domain @First p@ is an 'Arrow', and if for every @a@, @p a@ is an
-- instance of 'Applicative', then a pure arrow 'arr f' should correspond to
-- an "applicative natural transformation":
--
-- @
-- lmap (arr f) (p <*> q)
-- =
-- lmap (arr f) p <*> lmap (arr f) q
-- @
--
-- @
-- lmap (arr f) (pure a)
-- =
-- pure a
-- @
--
-- The following may not be true in general, but seems to hold in practice,
-- when the instance @'Applicative' (p a)@ orders effects from left to right,
-- in particular that should be the case if there is also a @'Monad' (p a)@:
--
-- @
-- lmap (first i) (lmap (arr fst) p <*> lmap (arr snd) q)
-- =
-- lmap (first i >>> arr fst) p <*> lmap (arr snd) q
-- @
--
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

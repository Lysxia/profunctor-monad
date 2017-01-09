{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module Profunctor.Monad.Profunctor
  ( Profunctor
  , Contravariant (..)
  , (=.)
  , (=:)
  , cofilter
  , J
  ) where

import Control.Applicative (Alternative)
import Control.Monad (guard)
import Control.Arrow (Kleisli(..), Arrow(..))
import Control.Category (Category, (>>>))
import Data.Functor (($>))
import Data.Constraint.Forall

infixl 5 =:, =.

-- | A 'Profunctor' is a bifunctor @p :: * -> * -> *@ from the product of an
-- arbitrary category, denoted @'First' p@, and @(->)@.
--
-- This is a generalization of the 'profunctors' package's @Profunctor@,
-- where @'First' p ~ (->)@.
--
-- A profunctor is two functors on different domains at once, one
-- contravariant, one covariant, and that is made clear by this definition
-- specifying 'Contravariant' and 'Functor' separately.
--
type Profunctor p = (Contravariant p, ForallF Functor p)

-- | Types @p :: * -> * -> *@ which are contravariant functors
-- over their first parameter.
--
-- Functor laws:
--
-- @
-- 'lmap' 'id' = 'id'
-- 'lmap' (i '>>>' j) = 'lmap' i '.' 'lmap' j
-- @
--
-- If the domain @'First' p@ is an 'Arrow', and if for every @a@, the type
-- @p a@ is an instance of 'Applicative', then a pure arrow 'arr' f should
-- correspond to an "applicative natural transformation":
--
-- @
-- 'lmap' ('arr' f) (p '<*>' q)
-- =
-- 'lmap' ('arr' f) p '<*>' 'lmap' ('arr' f) q
-- @
--
-- @
-- 'lmap' ('arr' f) ('pure' a) = 'pure' a
-- @
--
-- The following may not be true in general, but seems to hold in practice,
-- when the instance @'Applicative' (p a)@ orders effects from left to right,
-- in particular that should be the case if there is also a @'Monad' (p a)@:
--
-- @
-- 'lmap' ('first' i) ('lmap' ('arr' 'fst') p '<*>' 'lmap' ('arr' 'snd') q)
-- =
-- 'lmap' ('first' i '>>>' 'arr' 'fst') p '<*>' 'lmap' ('arr' 'snd') q
-- @
--
class Category (First p) => Contravariant p where
  -- | Domain of the functor.
  type First p :: * -> * -> *
  -- | Mapping morphisms from @'First' p@ to @(->)@.
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

cofilter
  :: (Contravariant p, First p ~ Kleisli m, Alternative m)
  => (x -> Bool) -> p x a -> p x a
cofilter p = (=:) (\x -> guard (p x) $> x)

-- | A type synonym to keep type signatures DRY. 'J' for "join".
--
-- @
-- J :: (* -> * -> *) -> (* -> *)
-- join :: Monad m => m (m a) -> (m a)
-- @
--
type J p a = p a a

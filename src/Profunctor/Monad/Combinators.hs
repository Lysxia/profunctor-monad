{- |
  Combinators for monadic profunctors using 'ForallF' to model quantified constraints
 -}

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Profunctor.Monad.Combinators where

import Control.Applicative
import Profunctor.Monad.Core
import Profunctor.Monad.Profunctor
import Data.List (head, tail)

-- * Basic combinators

-- | Instantiate a constraint @'ForallF' cc p@ at type @x@,
-- yielding @cc (p x)@.
--
-- === Usage
--
-- In some context with a constraint @'ForallF' 'Monad' p@ available:
--
-- @
-- 'with' \@'Monad' \@p @x '$' do
--   (...) :: p x a
-- @
--
with :: forall cc p x a. ForallF cc p => (cc (p x) => a) -> a
with a = case instF @cc @p @x of Sub Dict -> a

-- | A specialization of 'with' which deduces @p@ and @x@ from its argument.
--
-- === Usage
--
-- In some context with a constraint @'ForallF' 'Monad' p@ available:
--
-- @
-- 'with'' \@'Monad' '$' do
--   (...) :: p x a
-- @
with' :: forall cc p x a. ForallF cc p => (cc (p x) => p x a) -> p x a
with' = with @cc @p @x

-- | A specialization of 'with'' for 'Functor', to avoid @TypeApplications@
-- where this is possible.
--
-- === Usage
--
-- In some context with a constraint @'ForallF' 'Functor' p@ available:
--
-- @
-- 'withFunctor' '$'
--   (...) '<$>' (...)
-- @
withFunctor :: ForallF Functor p => (Functor (p x) => p x a) -> p x a
withFunctor = with' @Functor

-- | A specialization of 'with'' for 'Applicative', to avoid @TypeApplications@
-- where this is possible.
--
-- === Usage
--
-- In some context with a constraint @'ForallF' 'Applicative' p@ available:
--
-- @
-- 'withApplicative' '$'
--   (...) '<$>' (...) '<*>' (...)
-- @
withApplicative
  :: ForallF Applicative p => (Applicative (p x) => p x a) -> p x a
withApplicative = with' @Applicative

-- | A specialization of 'with'' for 'Alternative', to avoid @TypeApplications@
-- where this is possible.
--
-- === Usage
--
-- In some context with a constraint @'ForallF' 'Alternative' p@ available:
--
-- @
-- 'withAlternative' '$'
--   (...) '<|>' (...)
-- @
withAlternative
  :: ForallF Alternative p => (Alternative (p x) => p x a) -> p x a
withAlternative = with' @Alternative

-- | A specialization of 'with'' for 'Monad', to avoid @TypeApplications@ where
-- this is possible.
--
-- === Usage
--
-- In some context with a constraint @'ForallF' 'Alternative' p@ available:
--
-- @
-- 'withMonad' '$' do
--   (...)
-- @
withMonad :: ForallF Monad p => (Monad (p x) => p x a) -> p x a
withMonad = with' @Monad

-- | Bidirectional generalization of 'Control.Monad.replicateM'.
replicateP
  :: forall p x a
  .  (Profunctor p, ForallF Applicative p)
  => Int -> p x a -> p [x] [a]
replicateP = with @Applicative @p @[x] replicateP_

replicateP_
  :: (Profunctor p, Applicative (p [x]))
  => Int -> p x a -> p [x] [a]
replicateP_ 0 _ = pure []
replicateP_ n p = (:)
  <$> head =. p
  <*> tail =. replicateP_ (n - 1) p

manyP
  :: forall p x a
  .  (Profunctor p, ForallF Alternative p)
  => (([x] -> Bool) -> p [x] ()) -> p x a -> p [x] [a]
manyP = with @Alternative @p @[x] manyP_

manyP_
  :: (Profunctor p, Alternative (p [x]))
  => (([x] -> Bool) -> p [x] ()) -> p x a -> p [x] [a]
manyP_ assert p = someP_ assert p <|> pure []

someP
  :: forall p x a
  .  (Profunctor p, ForallF Alternative p)
  => (([x] -> Bool) -> p [x] ()) -> p x a -> p [x] [a]
someP = with @Alternative @p @[x] someP_

someP_
  :: (Profunctor p, Alternative (p [x]))
  => (([x] -> Bool) -> p [x] ()) -> p x a -> p [x] [a]
someP_ assert p =
  assert (not . null) *> liftA2 (:) (head =. p) (tail =. manyP_ assert p)

sepByP
  :: forall p x a b
  .  (Profunctor p, ForallF Alternative p)
  => (([x] -> Bool) -> p [x] ()) -> p x a -> p () b -> p [x] [a]
sepByP = with @Alternative @p @[x] sepByP_

sepByP_
  :: (Profunctor p, Alternative (p [x]))
  => (([x] -> Bool) -> p [x] ()) -> p x a -> p () b -> p [x] [a]
sepByP_ assert p s =
  (assert (not . null) *> sepBy1P_ assert p s) <|> pure []

sepBy1P
  :: forall p x a b
  .  (Profunctor p, ForallF Alternative p)
  => (([x] -> Bool) -> p [x] ()) -> p x a -> p () b -> p [x] [a]
sepBy1P = with @Alternative @p @[x] sepBy1P_

sepBy1P_
  :: (Profunctor p, Alternative (p [x]))
  => (([x] -> Bool) -> p [x] ()) -> p x a -> p () b -> p [x] [a]
sepBy1P_ assert p s = liftA2 (:) (head =. p) (tail =. preByP_ assert p s)

preByP
  :: forall p x a b
  .  (Profunctor p, ForallF Alternative p)
  => (([x] -> Bool) -> p [x] ()) -> p x a -> p () b -> p [x] [a]
preByP = with @Alternative @p @[x] preByP_

preByP_
  :: (Profunctor p, Alternative (p [x]))
  => (([x] -> Bool) -> p [x] ()) -> p x a -> p () b -> p [x] [a]
preByP_ assert p s =
  (assert (not . null) *> const () =. s *> sepBy1P_ assert p s) <|> pure []

{- |
  Combinators for monadic profunctors.
 -}

{-# LANGUAGE
    FlexibleContexts,
    ScopedTypeVariables,
    AllowAmbiguousTypes,
    TypeApplications,
    ConstraintKinds,
    PolyKinds,
    RankNTypes,
    QuantifiedConstraints #-}

module Profunctor.Monad.NewCombinators where

import Control.Applicative
import Profunctor.Monad.Partial

-- * Basic combinators

-- | Bidirectional generalization of 'Control.Monad.replicateM'.
replicateP
  :: (ProfunctorPartial p, Applicative (p [x]))
  => Int -> p x a -> p [x] [a]
replicateP 0 _ = pure []
replicateP n p = (:)
  <$> p `upon` headMaybe
  <*> replicateP (n - 1) p `upon` tailMaybe

headMaybe :: [a] -> Maybe a
headMaybe [] = Nothing
headMaybe (x : _) = Just x

tailMaybe :: [a] -> Maybe [a]
tailMaybe [] = Nothing
tailMaybe (_ : xs) = Just xs

manyP
  :: (ProfunctorPartial p, Alternative (p [x]))
  => (([x] -> Bool) -> p [x] ()) -> p x a -> p [x] [a]
manyP assert p = someP assert p <|> pure []

someP
  :: (ProfunctorPartial p, Alternative (p [x]))
  => (([x] -> Bool) -> p [x] ()) -> p x a -> p [x] [a]
someP assert p =
  assert (not . null) *> liftA2 (:) (headMaybe `comap` p) (tailMaybe `comap` manyP assert p)

sepByP
  :: (ProfunctorPartial p, Alternative (p [x]))
  => (([x] -> Bool) -> p [x] ()) -> p x a -> p () b -> p [x] [a]
sepByP assert p s =
  (assert (not . null) *> sepBy1P assert p s) <|> pure []

sepBy1P
  :: (ProfunctorPartial p, Alternative (p [x]))
  => (([x] -> Bool) -> p [x] ()) -> p x a -> p () b -> p [x] [a]
sepBy1P assert p s = liftA2 (:) (headMaybe `comap` p) (tailMaybe `comap` preByP assert p s)

preByP
  :: (ProfunctorPartial p, Alternative (p [x]))
  => (([x] -> Bool) -> p [x] ()) -> p x a -> p () b -> p [x] [a]
preByP assert p s =
  (assert (not . null) *> const () `lmap` s *> sepBy1P assert p s) <|> pure []

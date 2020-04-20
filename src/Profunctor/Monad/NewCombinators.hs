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

{-

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
-}

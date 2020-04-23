-- | Profunctors with a notion of failure on the contravariant side.

module Profunctor.Monad.Partial
  ( ProfunctorPartial(..)
  , comap
  , upon
  , upon'
  , (=.)
  , (=.?)
  , J

    -- * Reexported from profunctors
  , Profunctor(..)
  ) where

import Data.Profunctor

-- TODO: Find a better name?
class Profunctor p => ProfunctorPartial p where
  cofail :: p a b -> p (Maybe a) b

-- | Apply a partial function to the input of a computation. This is a contravariant map.
comap :: ProfunctorPartial p => (a -> Maybe a') -> p a' b -> p a b
comap f = lmap f . cofail

-- | Flipped version of 'comap'. Partial variant of 'upon''.
upon :: ProfunctorPartial p => p a' b -> (a -> Maybe a') -> p a b
upon = flip comap

-- | Flipped version of 'lmap'. Total variant of 'upon'.
upon' :: ProfunctorPartial p => p a' b -> (a -> a') -> p a b
upon' = flip lmap

infixl 7 `upon`, `upon'`

(=.) :: Profunctor p => (y -> x) -> p x a -> p y a
(=.) = lmap

infixr 5 =., =.?

(=.?) :: ProfunctorPartial p => (y -> Maybe x) -> p x a -> p y a
(=.?) = comap

-- | Abbreviation for types of the form @p a a@.
-- Named 'J' because this is the 'join' of the reader monad @(->)@.
type J p a = p a a

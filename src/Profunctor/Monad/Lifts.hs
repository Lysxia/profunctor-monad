{-# LANGUAGE FlexibleContexts #-}

module Profunctor.Monad.Lifts where

import Control.Category as Cat (id)
import Control.Arrow (Arrow, arr)
import Profunctor.Monad.Contravariant

-- |
--
-- @
-- lmap i (lifts p j)
-- =
-- lifts (lmap i p) (i >>> j)
-- @
--
-- @
-- lifts p i <*> lifts q j
-- =
-- lifts (p <*> q) (i &&& j >>> uncurry ($))
-- @
class Contravariant p => Lifts p where
  lifts :: p x a -> First p x a -> p x a

liftsArr
  :: (Lifts p, Arrow (First p))
  => p x a -> (x -> a) -> p x a
liftsArr p f = p `lifts` arr f

liftsId
  :: Lifts p => p a a -> p a a
liftsId p = p `lifts` Cat.id

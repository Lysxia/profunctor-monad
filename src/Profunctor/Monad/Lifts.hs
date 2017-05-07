{-# LANGUAGE FlexibleContexts #-}

module Profunctor.Monad.Lifts where

import qualified Control.Category as Cat
import Control.Arrow (Arrow(..))
import Profunctor.Monad.Cofunctor

-- |
--
-- @
-- 'lmap' i ('lifts' p j)
-- =
-- 'lifts' ('lmap' i p) (i 'Cat.>>>' j)
-- @
--
-- @
-- 'lifts' p i '<*>' 'lifts' q j
-- =
-- 'lifts' (p '<*>' q) (i '&&&' j 'Cat.>>>' 'uncurry' ('$'))
-- @
class Cofunctor p => Lifts p where
  lifts :: p x a -> First p x a -> p x a

liftsArr
  :: (Lifts p, Arrow (First p))
  => p x a -> (x -> a) -> p x a
liftsArr p f = p `lifts` arr f

liftsId
  :: Lifts p => p a a -> p a a
liftsId p = p `lifts` Cat.id

module Profunctor.Monad.Profunctor
  ( Profunctor(..)
  , (=.)
  ) where

import Data.Profunctor

(=.) :: Profunctor p => (y -> x) -> p x a -> p y a
(=.) = lmap

module Profunctor.Monad.Profunctor
  ( Profunctor(..)
  , (=.)
  , J
  ) where

import Data.Profunctor

(=.) :: Profunctor p => (y -> x) -> p x a -> p y a
(=.) = lmap

-- | A type synonym to keep type signatures DRY. 'J' for "join".
--
-- @
-- J :: (* -> * -> *) -> (* -> *)
-- join :: Monad m => m (m a) -> (m a)
-- @
--
type J p a = p a a

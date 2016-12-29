-- | Rebind syntax locally.
--
-- @
-- {-\# LANGUAGE RebindableSyntax \#-}
-- {-\# LANGUAGE RecordWildCards \#-}
--
-- -- Qualify to avoid polluting the namespace.
-- import qualified Profunctor.Monad.Syntax as S
--
-- let S.'Syntax'{..} = S.'promonad'
-- in do
--   ...
-- @

{-# LANGUAGE RankNTypes #-}

module Profunctor.Monad.Syntax where

import Data.Constraint.Forall (ForallF)
import Control.Monad.Fail (MonadFail)
import qualified Profunctor.Monad.Combinators as PM
import Prelude (String, Functor, Applicative, Monad)

data Syntax = Syntax
  { (<$>)
      :: forall p x a b
      . ForallF Functor p
      => (a -> b) -> p x a -> p x b

  , (<*>)
      :: forall p x a b
      .  ForallF Applicative p
      => p x (a -> b) -> p x a -> p x b

  , pure
      :: forall p x a
      .  ForallF Applicative p
      => a -> p x a

  , (<*)
      :: forall p x a b
      .  ForallF Applicative p
      => p x a -> p x b -> p x a

  , (*>)
      :: forall p x a b
      .  ForallF Applicative p
      => p x a -> p x b -> p x b

  , (>>=)
      :: forall p x a b
      .  ForallF Monad p
      => p x a -> (a -> p x b) -> p x b

  , (>>)
      :: forall p x a b
      .  ForallF Monad p
      => p x a -> p x b -> p x b

  , return
      :: forall p x a
      .  ForallF Monad p
      => a -> p x a

  , fail
      :: forall p x a
      .  ForallF MonadFail p
      => String -> p x a

  }

promonad :: Syntax
promonad = Syntax
  (PM.<$>)
  (PM.<*>)
  PM.pure
  (PM.<*)
  (PM.*>)
  (PM.>>=)
  (PM.>>)
  PM.return
  PM.fail


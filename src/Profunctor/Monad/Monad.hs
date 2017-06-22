{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Profunctor.Monad.Monad where

import qualified Control.Applicative as A
import qualified Control.Monad as M
import qualified Control.Monad.Fail as MF
import Profunctor.Monad.Combinators (with)
import Profunctor.Monad.Core
import Prelude (String)

-- * Rebound syntax

-- $rebindable Works with @RebindableSyntax@.

infixl 1 >>=, >>
infixl 4 <$>, <*>, <*, *>

(<$>)
  :: forall p x a b
  .  ForallF Functor p
  => (a -> b) -> p x a -> p x b
(<$>) = with @Functor @p @x (A.<$>)

(<*>)
  :: forall p x a b
  .  ForallF Applicative p
  => p x (a -> b) -> p x a -> p x b
(<*>) = with @Applicative @p @x (A.<*>)

pure
  :: forall p x a
  .  ForallF Applicative p
  => a -> p x a
pure = with @Applicative @p @x A.pure

(<*)
  :: forall p x a b
  .  ForallF Applicative p
  => p x a -> p x b -> p x a
(<*) = with @Applicative @p @x (A.<*)

(*>)
  :: forall p x a b
  .  ForallF Applicative p
  => p x a -> p x b -> p x b
(*>) = with @Applicative @p @x (A.*>)

(>>=)
  :: forall p x a b
  .  ForallF Monad p
  => p x a -> (a -> p x b) -> p x b
(>>=) = with @Monad @p @x (M.>>=)

(>>)
  :: forall p x a b
  .  ForallF Monad p
  => p x a -> p x b -> p x b
(>>) = with @Monad @p @x (M.>>)

return
  :: forall p x a
  .  ForallF Monad p
  => a -> p x a
return = with @Monad @p @x M.return

fail
  :: forall p x a
  .  ForallF MF.MonadFail p
  => String -> p x a
fail = with @MF.MonadFail @p @x MF.fail

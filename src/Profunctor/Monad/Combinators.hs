{- |
  Combinators for monadic profunctors.
 -}

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Profunctor.Monad.Combinators where

import qualified Control.Applicative as A
import Control.Arrow (Arrow)
import qualified Control.Monad as M
import Profunctor.Monad.Core
import Profunctor.Monad.Profunctor
import Data.Constraint
import Data.Constraint.Forall
import Prelude hiding (pure)

-- * Basic combinators

-- | Instantiate a constraint @'ForallF' cc p@ at type @x@,
-- yielding @cc (p x)@.
--
-- Usage example:
--
-- > f :: forall p x a. (ForallF Monad p, ...) => p x a
-- > f = with @Monad @p @x $ do monadicStuff
--
with :: forall cc p x a. ForallF cc p => (cc (p x) => a) -> a
with a = case instF @cc @p @x of Sub Dict -> a

-- | Bidirectional generalization of 'Control.Monad.replicateM'.
replicateP
  :: forall p x a
  .  (Contravariant p, Arrow (First p), ForallF Applicative p)
  => Int -> p x a -> p [x] [a]
replicateP = with @Applicative @p @[x] $
  let replicateP' 0 _ = A.pure []
      replicateP' n p = (:)
        A.<$> head =. p
        A.<*> tail =. replicateP (n - 1) p
  in replicateP'

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

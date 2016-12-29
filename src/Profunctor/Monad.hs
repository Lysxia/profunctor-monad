module Profunctor.Monad
  (
  -- * Constraints and standard type classes

    module Profunctor.Monad.Core

  -- * Contravariant functors

  , Contravariant (..)
  , (=.)
  , (=:)

  -- * Working with quantified constraints

  , with
  , with'
  , withFunctor, withApplicative, withAlternative, withMonad

  -- * Basic combinators

  , replicateP
  ) where

import Profunctor.Monad.Core
import Profunctor.Monad.Combinators
import Profunctor.Monad.Profunctor

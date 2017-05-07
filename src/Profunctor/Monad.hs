module Profunctor.Monad
  (
  -- * Constraints and standard type classes

    module Profunctor.Monad.Core
  , Profunctor (..)
  , (=.)


  -- * Working with quantified constraints

  , with
  , with'
  , withFunctor, withApplicative, withAlternative, withMonad

  -- * Miscellaneous combinators

  , replicateP

  ) where

import Profunctor.Monad.Core
import Profunctor.Monad.Combinators
import Profunctor.Monad.Profunctor

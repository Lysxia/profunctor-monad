{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Profunctor.Monad.MonadCoAction
  ( coAct
  , internaliseMaybe) where

import Data.Profunctor

-- | A right monad action on the contravariant parameter of a profunctor.
class (Profunctor p, Monad m) => MonadCoAction m p where
  coAct :: p u v -> p (m u) v

-- | 'coAct' with the Monad specialised to maybe as used in
--   "Composing Bidirectional Programs Monadically".
internaliseMaybe
  :: MonadCoAction Maybe p
  => p u v
  -> p (Maybe u) v
internaliseMaybe = coAct

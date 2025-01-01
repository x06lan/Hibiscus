{-# LANGUAGE FlexibleInstances #-}

module Hibiscus.TypeInfer.RSF (
    -- * The RSF monad
    RSF,
    -- * The RWS monad
    -- RWS,
    -- rws,
    -- runRWS,
    -- evalRWS,
    -- execRWS,
    -- mapRWS,
    -- withRWS,
    -- * The RWST monad transformer
    -- RWST,
    -- rwsT,
    -- runRWST,
    -- evalRWST,
    -- execRWST,
    -- mapRWST,
    -- withRWST,
    -- * Reader operations
    reader,
    ask,
    local,
    asks,
    -- * Writer operations
    -- writer,
    -- tell,
    -- listen,
    -- listens,
    -- pass,
    -- censor,
    -- * State operations
    state,
    get,
    put,
    modify,
    gets,
    -- * Fail operations
    Result,
    fail,
    -- * Lifting other operations
    liftCallCC,
    liftCallCC',
    liftCatch,
  ) where

import Control.Monad.Trans.RWS
import Control.Monad.Fail


type Result = Either String
instance MonadFail Result where
  fail = Left

-- MonadState + MonadReader + MonadFail
-- type RSF s e a = State s (ReaderT e Result a)

type RSF r s = RWST r () s Result

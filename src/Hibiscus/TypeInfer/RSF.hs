{-# LANGUAGE FlexibleInstances #-}

module Hibiscus.TypeInfer.RSF (
    -- * The RSF monad
    RSF,
    rsf,
    runRSF,
    evalRSF,
    execRSF,
    mapRSF, 
    withRSF,
    withRSF',
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
    -- liftCallCC,
    -- liftCallCC',
    -- liftCatch,
  ) where

import Control.Monad.Trans.RWS
import Control.Monad.Fail


type Result = Either String
instance MonadFail Result where
  fail = Left

-- newtype RWST r w s m a = RWST { runRWST :: r -> s -> m (a, s, w) }
-- MonadState + MonadReader + MonadFail
type RSF r s = RWST r () s Result

rsf :: (r -> s -> Result (a, s)) -> RSF r s a
rsf f = RWST (\r s -> (fmap (\(a, s) -> (a ,s, ())) $ f r s))

runRSF :: RSF r s a -> r -> s -> Result (a, s)
runRSF m r s = fmap (\(a, s, _) -> (a, s)) $ (runRWST m r s)

evalRSF :: RSF r s a -> r -> s -> Result a
evalRSF r s = fmap (fmap fst) $ runRSF r s

execRSF :: RSF r s a -> r -> s -> Result s
execRSF r s = fmap (fmap snd) $ runRSF r s

mapRSF :: ((a, s) -> (b, s)) -> RSF r s a -> RSF r s b
mapRSF f = mapRWST $ fmap (xmap f)
  where
    xmap :: ((a, s) -> (b, s)) -> (a, s, ()) -> (b, s, ())
    xmap g (a, s, _) = let (b, s') = g (a, s) in (b, s', ())

withRSF :: (r' -> s -> (r, s)) -> RSF r s a -> RSF r' s a
withRSF = withRWST

withRSF' :: (r -> s -> Result (r', s)) -> RSF r' s a -> RSF r s a
withRSF' f rsf = RWST $ \r s -> 
  case f r s of
    Left err -> fail err
    Right (r', s') ->
      do
        -- Run the original RSF with the transformed `r` and `s'`
        (a, s'', _) <- runRWST rsf r' s'
        return (a, s'', ())

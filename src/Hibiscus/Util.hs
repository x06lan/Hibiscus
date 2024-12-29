module Hibiscus.Util where

import Data.Foldable (foldlM, foldrM)


foldMaprM :: (Foldable t, Monad m, Monoid b) => (a -> m b) -> t a -> m b
foldMaprM f = foldrM aux mempty
  where
    aux a bcc = do
      b <- f a
      return $ b <> bcc

foldMaplM :: (Foldable t, Monad m, Monoid b) => (a -> m b) -> t a -> m b
foldMaplM f = foldlM aux mempty
  where
    aux bcc a = do
      b <- f a
      return $ bcc <> b

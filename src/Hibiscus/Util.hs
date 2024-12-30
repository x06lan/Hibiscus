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

-- If you don't care about the process order of the monad (state)
foldMapM :: (Foldable t, Monad m, Monoid b) => (a -> m b) -> t a -> m b
foldMapM = foldMaplM

replace :: Char -> Char -> String -> String
replace old new = map (\c -> if c == old then new else c) 

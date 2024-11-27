{-# LANGUAGE DeriveFoldable #-}

module Ast where

import Data.ByteString.Lazy.Char8 (ByteString)

data Name a
    = Name a ByteString
    deriving (Foldable, Show)

data Type a
    = TVar a (Name a)
    deriving (Foldable, Show)

data Argument a
    = Argument a (Name a) (Maybe (Type a))
    deriving (Foldable, Show)

data Dec a
    = Dec a (Name a) [Argument a] (Maybe (Type a)) (Expr a)
    deriving (Foldable, Show)

data Expr a
    = EInt a Integer
    | EVar a (Name a)
    | EString a ByteString
    deriving (Foldable, Show)

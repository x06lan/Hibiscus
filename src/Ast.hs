{-# LANGUAGE DeriveFoldable #-}

module Ast where

import Data.ByteString.Lazy.Char8 (ByteString)

data Name a
    = Name a ByteString
    deriving (Foldable, Show)

instance Eq (Name a) where
  (Name _ s1) == (Name _ s2) = s1 == s2

data Type a
    = TVar a (Name a)
    | TPar a (Type a)
    | TApp a (Type a)
    | TUnit a
    | TList a (Type a)
    | TArrow a (Type a) (Type a)
    | TLit a ByteString
    deriving (Foldable, Show)

instance Eq (Type a) where
  t1 == t2 = undefined

data Argument a
    = Argument a (Name a) (Maybe (Type a))
    deriving (Foldable, Show)

data Dec a
    = Dec a (Name a) [Argument a] (Expr a)
    | DecAnno a (Name a) (Type a)
    deriving (Foldable, Show)

data Expr a
    = EInt a Int
    | EFloat a Float
    | EVar a (Name a)
    | EString a ByteString
    | EUnit a
    | EList a [Expr a]
    | EPar a (Expr a)
    | EApp a (Expr a) (Expr a)
    | EIfThenElse a (Expr a) (Expr a) (Expr a)
    | ENeg a (Expr a)
    | EBinOp a (Expr a) (Op a) (Expr a)
    | EOp a (Op a)
    | ELetIn a (Dec a) (Expr a)
    deriving (Foldable, Show)

data Op a
    = Plus a
    | Minus a
    | Times a
    | Divide a
    | Eq a
    | Neq a
    | Lt a
    | Le a
    | Gt a
    | Ge a
    | And a
    | Or a
    deriving (Foldable, Show)

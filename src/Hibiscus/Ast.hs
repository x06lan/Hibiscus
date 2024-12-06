{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}

module Hibiscus.Ast where

import Data.ByteString.Lazy.Char8 (ByteString, unpack)

data Name a
    = Name a ByteString
    deriving (Foldable, Show, Functor)

instance Eq (Name a) where
  (Name _ s1) == (Name _ s2) = s1 == s2

data Type a
    = TVar a (Name a)
    | TPar a (Type a)
    | TApp a (Type a)
    | TUnit a
    | TList a (Type a)
    | TArrow a (Type a) (Type a)
    | TUnknown a Int
    deriving (Foldable, Functor)

prettyT (TArrow _ ta tb) = prettyT ta ++ " -> " ++ prettyT tb
prettyT (TVar _ (Name _ n)) = unpack n
prettyT (TUnknown _ s) = "?" ++ show s
prettyT t = show t

instance Show (Type a) where
  show t = "Type \"" ++ prettyT t ++ "\""

instance Eq (Type a) where
  (TVar _ n1)        == (TVar _ n2)        = n1 == n2
  (TPar _ t1)        == t2                 = t1 == t2
  t1                 == (TPar _ t2)        = t1 == t2
  (TUnit _)          == (TUnit _)          = True
  (TList _ t1)       == (TList _ t2)       = t1 == t2
  (TArrow _ t1a t1b) == (TArrow _ t2a t2b) = t1a == t2a && t1b == t2b
  _                  == _                  = False

data Argument a
    = Argument a (Name a)
    deriving (Foldable, Show, Functor)

data Dec a
    = Dec a (Name a) [Argument a] (Expr a)
    | DecAnno a (Name a) (Type a)
    deriving (Foldable, Show, Functor)

data Expr a
    = EInt a Int
    | EFloat a Float
    | EVar a (Name a)
    | EString a ByteString
    | EBool a Bool
    | EUnit a
    | EList a [Expr a]
    | EPar a (Expr a)
    | EApp a (Expr a) (Expr a)
    | EIfThenElse a (Expr a) (Expr a) (Expr a)
    | ENeg a (Expr a)
    | EBinOp a (Expr a) (Op a) (Expr a)
    | EOp a (Op a)
    | ELetIn a [Dec a] (Expr a)
    deriving (Foldable, Show, Functor)

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
    deriving (Foldable, Show, Functor)

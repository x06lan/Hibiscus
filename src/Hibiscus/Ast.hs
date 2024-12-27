{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}

module Hibiscus.Ast where

import Data.ByteString.Lazy.Char8 (ByteString, unpack)

data Name a
  = Name a ByteString
  deriving (Functor, Foldable, Ord)

instance Eq (Name a) where
  (Name _ s1) == (Name _ s2) = s1 == s2

instance Show (Name a) where
  show (Name _ b) = "Name " ++ show b

type MetaSymbol = Int

data Type a
  = TVar a (Name a)
  | TPar a (Type a)
  | TApp a (Type a)
  | TUnit a
  | TList a (Type a)
  | TArrow a (Type a) (Type a)
  | TUnknown a MetaSymbol
  deriving (Functor, Foldable)

instance Eq (Type a) where
  (TVar _ n1) == (TVar _ n2) = n1 == n2
  (TPar _ t1) == t2 = t1 == t2
  t1 == (TPar _ t2) = t1 == t2
  (TUnit _) == (TUnit _) = True
  (TList _ t1) == (TList _ t2) = t1 == t2
  (TArrow _ t1a t1b) == (TArrow _ t2a t2b) = t1a == t2a && t1b == t2b
  _ == _ = False

instance Show (Type a) where
  show (TVar _ (Name _ n)) = unpack n
  show (TPar _ t) = "(" ++ show t ++ ")"
  show (TUnit _) = "Unit"
  show (TList _ t) = "List " ++ show t
  show (TArrow _ ta tb) = show ta ++ " -> " ++ show tb
  show (TUnknown _ s) = "?" ++ show s

data Argument a
  = Argument a (Name a)
  deriving (Functor, Foldable, Show)

data Dec a
  = Dec a (Name a) [Argument a] (Expr a)
  | DecAnno a (Name a) (Type a)
  deriving (Functor, Foldable, Show)

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
  deriving (Functor, Foldable, Show)

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
    deriving (Eq, Functor, Foldable, Show)

-- NOTE: Hardcode 
isBooleanOp :: Op a -> Bool
isBooleanOp (Eq _) = True
isBooleanOp (Neq _) = True
isBooleanOp (Lt _) = True
isBooleanOp (Le _) = True
isBooleanOp (Gt _) = True
isBooleanOp (Ge _) = True
isBooleanOp _ = False

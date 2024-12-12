module Hibiscus.Typing where

import Data.List (intercalate)
import Hibiscus.Asm (StorageClass)

-- import qualified Data.Set as Set

data DataType
  = DTypeVoid
  | DTypeBool
  | DTypeInt Int Int
  | DTypeFloat Int -- size
  | DTypeVector Int DataType -- size, type
  | DTypeMatrix Int DataType -- col size, col type
  | DTypeArray Int DataType -- size, type
  | DTypePointer StorageClass DataType -- pointer type
  | DTypeStruct String [DataType] -- name, fields
  | DTypeFunction DataType [DataType] -- return type, arguments
  deriving (Eq)

instance Show DataType where
  show DTypeVoid = "void"
  show DTypeBool = "bool"
  show (DTypeInt size sign) =
    case sign of
      0 -> "ui" ++ show size
      1 -> "i" ++ show size
      _ -> error "Invalid sign"
  show (DTypeFloat size) = "f" ++ show size
  show (DTypeVector size baseType) = "vec" ++ show size ++ show baseType
  show (DTypeMatrix col baseType) = "mat" ++ show col ++ show baseType
  show (DTypeArray size baseType) = "arr_" ++ show size ++ show baseType
  show (DTypePointer storage baseType) = "ptr_" ++ show baseType ++ show storage
  show (DTypeStruct name fields) = "struct_" ++ name ++ "_" ++ intercalate "_" (map show fields)
  show (DTypeFunction returnType args) = "func_" ++ intercalate "_" (map show args) ++ "_" ++ show returnType

bool :: DataType
bool = DTypeBool

uint32 :: DataType
uint32 = DTypeInt 32 0

int32 :: DataType
int32 = DTypeInt 32 1

float32 :: DataType
float32 = DTypeFloat 32

vector2 :: DataType
vector2 = DTypeVector 2 float32

vector3 :: DataType
vector3 = DTypeVector 4 float32

vector4 :: DataType
vector4 = DTypeVector 4 float32
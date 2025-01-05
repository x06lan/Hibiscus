module Hibiscus.CodeGen.Type.DataType where

import qualified Data.ByteString.Lazy.Char8 as BS
import Data.List (intercalate)
import qualified Hibiscus.Asm as Asm
import qualified Hibiscus.Ast as Ast

-- import qualified Data.Set as Set

data DataType
  = DTypeUnknown
  | DTypeVoid
  | DTypeBool
  | DTypeInt Int
  | DTypeUInt Int
  | DTypeFloat Int -- size
  | DTypeVector Int DataType -- size, type
  | DTypeMatrix Int DataType -- col size, col type
  | DTypeLengthUnknownArray DataType -- HACK:
  | DTypeArray Int DataType -- size, type
  | DTypePointer Asm.StorageClass DataType -- pointer type
  | DTypeStruct String [DataType] -- name, fields
  | DTypeFunction DataType [DataType] -- return type, arguments
  deriving (Eq, Ord)

instance Show DataType where
  show DTypeUnknown = "unknown"
  show DTypeVoid = "void"
  show DTypeBool = "bool"
  show (DTypeInt size) = "i" ++ show size
  show (DTypeUInt size) = "ui" ++ show size
  show (DTypeFloat size) = "f" ++ show size
  show (DTypeVector size baseType) = "v" ++ show size ++ show baseType
  show (DTypeMatrix col baseType) = "mat" ++ show col ++ show baseType
  show (DTypeLengthUnknownArray baseType) = "len_unknown_arr_" ++ show baseType
  show (DTypeArray size baseType) = "arr_" ++ show size ++ show baseType
  show (DTypePointer storage baseType) = "ptr_" ++ show baseType ++ "_" ++ show storage
  show (DTypeStruct name fields) = "struct_" ++ name ++ "_" ++ intercalate "_" (map show fields)
  show (DTypeFunction returnType args) = "func_" ++ intercalate "_" (map show args) ++ "_" ++ show returnType

bool :: DataType
bool = DTypeBool

uint32 :: DataType
uint32 = DTypeUInt 32

int32 :: DataType
int32 = DTypeInt 32

float32 :: DataType
float32 = DTypeFloat 32

vector2 :: DataType
vector2 = DTypeVector 2 float32

vector3 :: DataType
vector3 = DTypeVector 3 float32

vector4 :: DataType
vector4 = DTypeVector 4 float32

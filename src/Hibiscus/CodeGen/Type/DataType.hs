module Hibiscus.CodeGen.Type.DataType where

import qualified Data.ByteString.Lazy.Char8 as BS
import Data.List (intercalate)
import Hibiscus.Asm (StorageClass)
import qualified Hibiscus.Ast as Ast
import Hibiscus.Lexer
import Hibiscus.Parser

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
  | DTypeArray Int DataType -- size, type
  | DTypePointer StorageClass DataType -- pointer type
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

typeFunctionConvert :: Ast.Type ()-> DataType
typeFunctionConvert t = case t of
  Ast.TArrow _ t1 t2 ->
    let processArrow :: Ast.Type () -> ([DataType], DataType)
        processArrow (Ast.TArrow _ t1' t2') =
          let (args, ret) = processArrow t2'
           in (typeConvert t1' : args, ret)
        processArrow t = ([], typeConvert t)

        (argTypes, returnType) = processArrow t
     in DTypeFunction returnType argTypes
  _ -> error ("Not a function type" ++ show t)

typeConvert :: Ast.Type () -> DataType
typeConvert t = case t of
  Ast.TVar _ (Ast.Name _ n) -> case typeStringConvert (BS.unpack n) of
    Just x -> x
    Nothing -> error ("Not implemented" ++ show t)
  Ast.TPar _ t -> typeConvert t
  Ast.TArrow _ t1 t2 -> typeFunctionConvert t
  Ast.TApp _ t -> error ("Not implemented App" ++ show t)
  Ast.TUnit _ -> DTypeVoid
  _ -> error ("Not implemented?" ++ show t)

typeStringConvert :: String -> Maybe DataType
typeStringConvert t = case t of
  "Int" -> Just int32
  "Float" -> Just float32
  "Bool" -> Just bool
  "Vec2" -> Just vector2
  "Vec3" -> Just vector3
  "Vec4" -> Just vector4
  -- "int" -> Just int32
  -- "float" -> Just float32
  -- "bool" -> Just bool
  -- "vec2" -> Just vector2
  -- "vec3" -> Just vector3
  -- "vec4" -> Just vector4
  _ -> Nothing

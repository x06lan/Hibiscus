module Hibiscus.CodeGen.Type.Bulitin where

import Hibiscus.CodeGen.Types
import Hibiscus.CodeGen.Type.DataType

getBulitinFunction :: String -> FunctionSignature -> Maybe ExprReturn
getBulitinFunction name (returnType, args) = 
  let
    magic ft = ExprApplication ft (returnType, args) []
    justMagic = return . magic
  in  
  case name of
    "Int" ->       justMagic $ TypeConstructor returnType
    "Float" ->     justMagic $ TypeConstructor returnType
    "Bool" ->      justMagic $ TypeConstructor returnType
    "Vec2" ->      justMagic $ TypeConstructor returnType
    "Vec3" ->      justMagic $ TypeConstructor returnType
    "Vec4" ->      justMagic $ TypeConstructor returnType
    "foldl" ->     justMagic $ FunctionFoldl 
    "map" ->       justMagic $ FunctionMap 
    "extract_0" -> justMagic $ TypeExtractor returnType [0]
    "extract_1" -> justMagic $ TypeExtractor returnType [1]
    "extract_2" -> justMagic $ TypeExtractor returnType [2]
    "extract_3" -> justMagic $ TypeExtractor returnType [3]
    _ -> Nothing

getBulitinType :: String -> Maybe DataType
getBulitinType t = case t of
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

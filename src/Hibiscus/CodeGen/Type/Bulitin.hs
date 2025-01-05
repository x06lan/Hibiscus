module Hibiscus.CodeGen.Type.Bulitin where

import Hibiscus.CodeGen.Types
import Hibiscus.CodeGen.Type.DataType

getBulitinFunctionType :: String -> Maybe BaseFunctionType
getBulitinFunctionType name = 
  case name of
    "Int" ->       return $ TypeConstructor int32
    "Float" ->     return $ TypeConstructor float32
    "Bool" ->      return $ TypeConstructor bool
    "Vec2" ->      return $ TypeConstructor vector2
    "Vec3" ->      return $ TypeConstructor vector3
    "Vec4" ->      return $ TypeConstructor vector4
    "foldl" ->     return $ FunctionFoldl 
    "map" ->       return $ FunctionMap 
    "extract_0" -> return $ TypeExtractor float32 [0]
    "extract_1" -> return $ TypeExtractor float32 [1]
    "extract_2" -> return $ TypeExtractor float32 [2]
    "extract_3" -> return $ TypeExtractor float32 [3]
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

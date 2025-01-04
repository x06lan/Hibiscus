module Hibiscus.CodeGen.Constants where

import qualified Hibiscus.Asm as Asm
import qualified Hibiscus.CodeGen.Type.DataType as DT
import Hibiscus.CodeGen.Types


defaultConfig :: Config
defaultConfig =
  Config
    { capability = Asm.Shader
    , addressModel = Asm.Logical
    , memoryModel = Asm.GLSL450
    , source = (Asm.GLSL, 450)
    , shaderType = Asm.Fragment
    , executionMode = Asm.OriginUpperLeft
    , extension = "GLSL.std.450"
    , entryPoint = "main"
    -- uniforms = [("uv", vector2, Input, 0), ("outColor", vector4, Output, 0)]
    }

global :: (String, DT.DataType)
global = ("", DT.DTypeVoid)

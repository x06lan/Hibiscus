{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-missing-signatures #-}

module Hibiscus.CodeGen.Type where

-- import qualified Data.Set as Set

import Control.Exception (handle)
import qualified Data.ByteString.Lazy.Char8 as BS
import Data.List (find, intercalate)
import qualified Data.Map as Map
import Data.Maybe
import Data.STRef (newSTRef)
import Debug.Trace
import Hibiscus.Asm
import qualified Hibiscus.Ast as Ast
import Hibiscus.Lexer
import Hibiscus.Parser
import Hibiscus.CodeGen.Type.DataType

import qualified Hibiscus.Type4plus as TI -- type infer

import Control.Monad.State.Lazy
import Data.Monoid (First (..), getFirst)

import Hibiscus.Util (foldMaplM, foldMaprM)

-- IDK why this is not imported from Asm
type ResultId = OpId

-- import Data.IntMap (fromList, foldlWithKey)

----- Instruction constructor helpers BEGIN -----

noReturnInstruction :: Ops -> Instruction
noReturnInstruction op = Instruction (Nothing, op)

returnedInstruction :: ResultId -> Ops -> Instruction
returnedInstruction id op = Instruction (Just id, op)

commentInstruction :: String -> Instruction
commentInstruction = noReturnInstruction . Comment

----- Instruction constructor helpers END -------

type Variable = (OpId, DataType)

type Uniform = (String, DataType, StorageClass, Int)

type Type = Ast.Type ()
type Dec = Ast.Dec (Range, Type)
type Expr = Ast.Expr (Range, Type)
type Argument = Ast.Argument (Range, Type)

getNameAndDType :: Argument -> (String, DataType)
getNameAndDType (Ast.Argument (_, t) (Ast.Name _ name)) = (BS.unpack name, typeConvert t)

type FunctionSignature = (DataType, [DataType]) -- return type, arguments

type Env = ([String], DataType) -- function name, function type

type ResultMap = Map.Map ResultType ExprReturn

-- type TypeInst = [Instruction]
-- type ConstInst = [Instruction]
-- type NameInst =[Instruction]
-- type UniformsInst =[Instruction]
type VariableInst = [Instruction]
type StackInst = [Instruction]

type VeryImportantTuple = (ExprReturn, Instructions, VariableInst, StackInst)

data Config = Config
  { capability :: Capability
  , extension :: String
  , memoryModel :: MemoryModel
  , addressModel :: AddressingModel
  , executionMode :: ExecutionMode
  , shaderType :: ExecutionModel
  , source :: (SourceLanguage, Int)
  , entryPoint :: String
  -- uniforms :: [Uniform] -- (name, type, position)
  }

data FunctionType
  = CustomFunction OpId String
  | TypeConstructor DataType -- function type constructor
  | TypeExtractor DataType [Int] -- function type decorator
  | OperatorFunction (Ast.Op (Range, Type))
  | FunctionFoldl -- base function
  | FunctionMap -- base function
  deriving (Show)

data ExprReturn
  = ExprResult Variable
  | ExprApplication FunctionType FunctionSignature [Variable] -- name function, arguments
  deriving (Show)

data ResultType
  = ResultDataType DataType -- done
  | ResultConstant Literal -- done
  | ResultVariable (Env, String, DataType) -- done
  | ResultVariableValue (Env, String, DataType) -- done
  | ResultFunction String FunctionSignature -- name return type, arguments
  | ResultCustom String -- done
  deriving (Show, Eq, Ord)

data LanxSt = LanxSt
  { idCount :: Int
  , idMap :: ResultMap
  , env :: Env
  , decs :: [Dec]
  }
  deriving (Show)

data HeaderFields = HeaderFields
  { capabilityInst :: Maybe Instruction
  , extensionInst :: Maybe Instruction
  , memoryModelInst :: Maybe Instruction
  , entryPointInst :: Maybe Instruction
  , executionModeInst :: Maybe Instruction
  , sourceInst :: Maybe Instruction
  }
  deriving (Show)

emptyHeaderFields =
  HeaderFields
    { capabilityInst = Nothing
    , extensionInst = Nothing
    , memoryModelInst = Nothing
    , entryPointInst = Nothing
    , executionModeInst = Nothing
    , sourceInst = Nothing
    }

fromHeaderFields :: HeaderFields -> [Instruction]
fromHeaderFields hf =
  [ commentInstruction "header fields"
  , fromJust (capabilityInst hf)
  , fromJust (extensionInst hf)
  , fromJust (memoryModelInst hf)
  , fromJust (entryPointInst hf)
  , fromJust (executionModeInst hf)
  , fromJust (sourceInst hf)
  ]

data FunctionInst = FunctionInst
  { begin :: [Instruction]
  , parameter :: [Instruction]
  , label :: [Instruction]
  , variable :: [Instruction]
  , body :: [Instruction]
  , end :: [Instruction]
  }
  deriving (Show)

data Instructions = Instructions
  { headerFields :: HeaderFields -- HACK: Maybe
  , nameFields :: [Instruction]
  , uniformsFields :: [Instruction]
  , typeFields :: [Instruction]
  , constFields :: [Instruction]
  , functionFields :: [FunctionInst] -- [function]
  }
  deriving (Show)

dtypeof :: Literal -> DataType
dtypeof (LBool _)  = bool
dtypeof (LUint _)  = uint32
dtypeof (LInt _)   = int32
dtypeof (LFloat _) = float32

-- FIXME: AFAIK, Instructions don’t actually form a Monoid.
--        However, since most folds are associative, I created this instance
--        to leverage Monoid for folding, making it less mentally taxing to work with.
--        USE WITH CAUTION.
instance Semigroup Instructions where
  (<>) = (+++)
instance Monoid Instructions where
  mempty = emptyInstructions

(+++) :: Instructions -> Instructions -> Instructions
(Instructions h1 n1 u1 t1 c1 f1) +++ (Instructions h2 n2 u2 t2 c2 f2) =
  Instructions (h1 `merge` h2) (n1 ++ n2) (u1 ++ u2) (t1 ++ t2) (c1 ++ c2) (f1 ++ f2)
 where
  mergeMaybe h Nothing = h
  mergeMaybe Nothing h = h
  mergeMaybe _ _ = error "fuck"

  merge :: HeaderFields -> HeaderFields -> HeaderFields
  merge hf1 hf2 =
    HeaderFields
      { capabilityInst = mergeMaybe (capabilityInst hf1) (capabilityInst hf2)
      , extensionInst = mergeMaybe (extensionInst hf1) (extensionInst hf2)
      , memoryModelInst = mergeMaybe (memoryModelInst hf1) (memoryModelInst hf2)
      , entryPointInst = mergeMaybe (entryPointInst hf1) (entryPointInst hf2)
      , executionModeInst = mergeMaybe (executionModeInst hf1) (executionModeInst hf2)
      , sourceInst = mergeMaybe (sourceInst hf1) (sourceInst hf2)
      }

-- FIXME: fucked up semantics

defaultConfig :: Config
defaultConfig =
  Config
    { capability = Shader
    , addressModel = Logical
    , memoryModel = GLSL450
    , source = (GLSL, 450)
    , shaderType = Fragment
    , executionMode = OriginUpperLeft
    , extension = "GLSL.std.450"
    , entryPoint = "main"
    -- uniforms = [("uv", vector2, Input, 0), ("outColor", vector4, Output, 0)]
    }

emptyInstructions :: Instructions
emptyInstructions =
  Instructions
    { headerFields = emptyHeaderFields -- FIXME:
    , nameFields = []
    , uniformsFields = []
    , typeFields = []
    , constFields = []
    , functionFields = []
    }
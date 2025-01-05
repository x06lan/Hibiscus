{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-missing-signatures #-}

module Hibiscus.CodeGen.Types where

-- import qualified Data.Set as Set

import Control.Exception (handle)

-- type infer
import Control.Monad.State.Lazy
import qualified Data.ByteString.Lazy.Char8 as BS
import Data.List (find, intercalate)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid (First (..), getFirst)
import Data.STRef (newSTRef)
import qualified Hibiscus.Asm as Asm
import qualified Hibiscus.Ast as Ast
import Hibiscus.CodeGen.Type.DataType (DataType)
import qualified Hibiscus.CodeGen.Type.DataType as DT
import qualified Hibiscus.Parsing.Lexer as L
import qualified Hibiscus.TypeInfer as TI
import Hibiscus.Util (foldMaplM, foldMaprM, replace)
import Data.Type.Bool (If)


----- Instruction constructor helpers BEGIN -----

noReturnInstruction :: Asm.Ops -> Asm.Instruction
noReturnInstruction op = Asm.Instruction (Nothing, op)

returnedInstruction :: Asm.ResultId -> Asm.Ops -> Asm.Instruction
returnedInstruction id op = Asm.Instruction (Just id, op)

commentInstruction :: String -> Asm.Instruction
commentInstruction = noReturnInstruction . Asm.Comment

----- Instruction constructor helpers END -------

type VeryImportantTuple = (ExprReturn, Instructions, VariableInst, StackInst)

type Variable = (Asm.OpId, DataType)

type Uniform = (String, DataType, Asm.StorageClass, Int)

type Type = Ast.Type ()
type Dec = Ast.Dec (L.Range, Type)
type Expr = Ast.Expr (L.Range, Type)
type Argument = Ast.Argument (L.Range, Type)

type FunctionSignature = (DataType, [DataType]) -- return type, arguments

type Env = [(String, DataType)] -- function name, function type

type ResultMap = Map.Map ResultType ExprReturn

-- type TypeInst = [Instruction]
-- type ConstInst = [Instruction]
-- type NameInst =[Instruction]
-- type UniformsInst =[Instruction]
type VariableInst = [Asm.Instruction]
type StackInst = [Asm.Instruction]


data Config = Config
  { capability :: Asm.Capability
  , extension :: String
  , memoryModel :: Asm.MemoryModel
  , addressModel :: Asm.AddressingModel
  , executionMode :: Asm.ExecutionMode
  , shaderType :: Asm.ExecutionModel
  , source :: (Asm.SourceLanguage, Int)
  , entryPoint :: String
  -- uniforms :: [Uniform] -- (name, type, position)
  }

data BaseFunctionType
  = CustomFunction Asm.OpId String
  | TypeConstructor DataType -- function type constructor
  | TypeExtractor DataType [Int] -- function type decorator
  | OperatorFunction (Ast.Op (L.Range, Type))
  | FunctionFoldl -- base function
  | FunctionMap -- base function
  deriving (Show)

data FunctionType
  = BaseFunction BaseFunctionType
  | IfElseApplication Expr Expr Expr  -- if, then, else
  deriving (Show)

data ExprReturn
  = ExprResult Variable
  | ExprApplication FunctionType FunctionSignature [Variable] -- name function, arguments
  deriving (Show)

data ResultType
  = ResultDataType DataType -- done
  | ResultConstant Asm.Literal -- done
  | ResultVariable (Env, String, DataType) -- done
  | ResultVariableValue (Env, String, DataType) -- done
  | -- | ResultFunction String FunctionSignature -- name return type, arguments
    ResultCustom String -- done
  deriving (Show, Eq, Ord)

data LanxSt = LanxSt
  { idCount :: Int
  , idMap :: ResultMap
  , env :: Env
  , decs :: [Dec]
  }
  deriving (Show)

nextOpId :: State LanxSt Asm.OpId
nextOpId =
  do
    modify (\s -> s{idCount = idCount s + 1})
    gets (Asm.Id . idCount)

nextOpIdName :: (Int -> String) -> State LanxSt Asm.OpId
nextOpIdName f =
  do
    modify (\s -> s{idCount = idCount s + 1})
    gets (Asm.IdName . f . idCount)

data HeaderFields = HeaderFields
  { capabilityInst :: Maybe Asm.Instruction
  , extensionInst :: Maybe Asm.Instruction
  , memoryModelInst :: Maybe Asm.Instruction
  , entryPointInst :: Maybe Asm.Instruction
  , executionModeInst :: Maybe Asm.Instruction
  , sourceInst :: Maybe Asm.Instruction
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

fromHeaderFields :: HeaderFields -> [Asm.Instruction]
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
  { begin :: [Asm.Instruction]
  , parameter :: [Asm.Instruction]
  , label :: [Asm.Instruction]
  , variable :: [Asm.Instruction]
  , body :: [Asm.Instruction]
  , end :: [Asm.Instruction]
  }
  deriving (Show)

data Instructions = Instructions
  { headerFields :: HeaderFields -- HACK: Maybe
  , nameFields :: [Asm.Instruction]
  , uniformsFields :: [Asm.Instruction]
  , typeFields :: [Asm.Instruction]
  , constFields :: [Asm.Instruction]
  , functionFields :: [FunctionInst] -- [function]
  }
  deriving (Show)

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

{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-missing-signatures #-}

module Hibiscus.CodeGen where

-- import qualified Data.Set as Set

import qualified Data.ByteString.Lazy.Char8 as BS
import Data.List (intercalate, find)
import qualified Data.Map as Map
import Data.Maybe
import Data.STRef (newSTRef)
import Debug.Trace
import Hibiscus.Asm
import qualified Hibiscus.Ast as Ast
import Hibiscus.Lexer
import Hibiscus.Parser
import Hibiscus.Typing
import Control.Exception (handle)

-- import Data.IntMap (fromList, foldlWithKey)

type Variable = (OpId, DataType)

type Uniform = (String, DataType, StorageClass, Int)

type Type = Ast.Type ()
type Dec = Ast.Dec (Range, Type)
type Expr = Ast.Expr (Range, Type)
type Argument = Ast.Argument (Range, Type)

type FunctionSignature = (DataType, [DataType]) -- return type, arguments

type Env = ([String], DataType) -- function name, function type

type ResultMap = Map.Map ResultType ExprReturn

-- type TypeInst = [Instruction]
-- type ConstInst = [Instruction]
-- type NameInst =[Instruction]
-- type UniformsInst =[Instruction]
type VariableInst= [Instruction]
type StackInst= [Instruction]


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

data State = State
  { idCount :: Int,
    idMap :: ResultMap,
    env :: Env,
    decs :: [Dec]
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
  [ Instruction (Nothing, Comment "header fields")
  , fromJust (capabilityInst hf)
  , fromJust (extensionInst hf)
  , fromJust (memoryModelInst hf)
  , fromJust (entryPointInst hf)
  , fromJust (executionModeInst hf)
  , fromJust (sourceInst hf)
  ]

data FunctionInst= FunctionInst{
  begin :: [Instruction],
  parameter :: [Instruction],
  label :: [Instruction],
  variable :: [Instruction],
  body :: [Instruction],
  end :: [Instruction]
}deriving(Show)

data Instructions = Instructions
  { headerFields :: HeaderFields -- HACK: Maybe
  , nameFields :: [Instruction]
  , uniformsFields :: [Instruction]
  , typeFields :: [Instruction]
  , constFields :: [Instruction]
  , functionFields :: [FunctionInst] -- [function]
  }
  deriving (Show)

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

findResult :: State -> ResultType -> Maybe ExprReturn
findResult s key = 
  case key of 
    ResultVariable ((envs, envType), name, varType) ->  -- find variable up to the mother env
      let 
        (result,envs') = foldl (\(acc_result ,acc_env) env -> 
          case acc_result of 
            Just x -> (Just x, acc_env)
            Nothing -> (Map.lookup (ResultVariable ((acc_env++[env], envType), name, varType)) (idMap s), acc_env++[env])
          ) (Nothing,[]) envs
       in result
    ResultVariableValue ((envs, envType), name, varType) ->  -- find variable up to the mother env
      let 
        (result,envs') = foldl (\(acc_result ,acc_env) env -> 
          case acc_result of 
            Just x -> (Just x, acc_env)
            Nothing -> (Map.lookup (ResultVariableValue ((acc_env++[env], envType), name, varType)) (idMap s), acc_env++[env])
          ) (Nothing,[]) envs
       in result
    _ -> Map.lookup key (idMap s)


insertResult :: State -> ResultType -> Maybe ExprReturn -> (State, ExprReturn)
insertResult state key Nothing =
  case findResult state key of
    Just existingResult -> (state, existingResult)
    Nothing ->
      let (newMap, newId, newCount) = generateEntry state key
          updatedState = state{idMap = newMap, idCount = newCount}
       in (updatedState, newId)
-- error (show key ++ " not found")
insertResult state key (Just value) =
  case findResult state key of
    Just existingResult -> (state, existingResult)
    Nothing ->
      let newMap = Map.insert key value (idMap state)
          updatedState = state{idMap = newMap}
       in (updatedState, value)

-- Helper function to generate a new entry for the IdType
generateEntry :: State -> ResultType -> (ResultMap, ExprReturn, Int)
generateEntry state key =
  let currentMap = idMap state
      currentCount = idCount state
   in case key of
        ResultDataType t ->
          let var = (IdName (show t), t)
              result = ExprResult var
           in (Map.insert key result currentMap, result, currentCount)
        ResultConstant l ->
          let var = case l of
                LBool b -> (IdName ("bool_" ++ show b), DTypeBool)
                LUint i -> (IdName ("uint_" ++ show i), uint32)
                LInt i -> (IdName ("int_" ++ show i), int32)
                LFloat f -> (IdName ("float_" ++ map (\c -> if c == '.' then '_' else c) (show f)), float32)
              result = ExprResult var
           in (Map.insert key result currentMap, result, currentCount)
        ResultVariable ((envs, envType), name, varType) ->
          let var = (IdName (intercalate "_" (envs++[name])), varType)
              result = ExprResult var
           in (Map.insert key result currentMap, result, currentCount)
        ResultVariableValue ((envName, envType), s, varType) ->
          let var = (Id (currentCount + 1), varType)
              result = ExprResult var
           in (Map.insert key result currentMap, result, currentCount + 1)
        ResultFunction s (return, args) ->
          let t = DTypeFunction return args
              var = (IdName (intercalate "_" (s : map show args)), t)
              result = ExprResult var
           in (Map.insert key result currentMap, result, currentCount)

searchTypeId :: State -> DataType -> OpId
searchTypeId s dt = case findResult s (ResultDataType dt) of
  Just x -> case x of
    ExprResult (id, _) -> id
    _ -> error (show dt ++ " type not found")
  Nothing -> error (show dt ++ " type not found")

generateType :: State -> DataType -> (State, OpId, Instructions)
generateType state dType =
  case findResult state (ResultDataType dType) of
    Just (ExprResult (typeId, _)) -> (state, typeId, emptyInstructions)
    Nothing ->
      let (state1, inst) = case dType of
            DTypeUnknown -> error "Unknown type"
            DTypeVoid -> (state, emptyInstructions)
            DTypeBool -> (state, emptyInstructions)
            DTypeInt _ -> (state, emptyInstructions)
            DTypeUInt _ -> (state, emptyInstructions)
            DTypeFloat _ -> (state, emptyInstructions)
            DTypeVector _ baseType -> let (s', id, inst') = generateType state baseType in (s', inst')
            DTypeMatrix _ baseType -> let (s', id, inst') = generateType state baseType in (s', inst')
            DTypeArray _ baseType -> let (s', id, inst') = generateType state baseType in (s', inst')
            DTypePointer _ baseType -> let (s', id, inst') = generateType state baseType in (s', inst')
            -- FIXME: unsure what to modify here
            DTypeStruct _ fields -> foldl (\(s, inst') field -> let (s', id, inst'') = generateType s field in (s', inst' +++ inst'')) (state, emptyInstructions) fields
            DTypeFunction returnType argsType -> foldl (\(s, inst') t -> let (s', id, inst'') = generateType s (DTypePointer Function t) in (s', inst' +++ inst'')) (state, emptyInstructions) (returnType : argsType)
          (state2, ExprResult (typeId, _)) = insertResult state1 (ResultDataType dType) Nothing
          searchTypeId' = searchTypeId state2

          (state3, inst3) = case dType of
            DTypeUnknown -> error "Unknown type"
            DTypeVoid -> (state2, emptyInstructions{typeFields = [Instruction (Just typeId, OpTypeVoid)]})
            DTypeBool -> (state2, emptyInstructions{typeFields = [Instruction (Just typeId, OpTypeBool)]})
            DTypeInt size -> (state2, emptyInstructions{typeFields = [Instruction (Just typeId, OpTypeInt size 0)]})
            DTypeUInt size -> (state2, emptyInstructions{typeFields = [Instruction (Just typeId, OpTypeInt size 1)]})
            DTypeFloat size -> (state2, emptyInstructions{typeFields = [Instruction (Just typeId, OpTypeFloat size)]})
            DTypeVector size baseType -> (state2, emptyInstructions{typeFields = [Instruction (Just typeId, OpTypeVector (searchTypeId' baseType) size)]})
            DTypeMatrix col baseType -> (state2, emptyInstructions{typeFields = [Instruction (Just typeId, OpTypeMatrix (searchTypeId' baseType) col)]})
            DTypeArray size baseType ->
              let (state4, constId, inst2) = generateConst state3 (LUint size)
                  arrayInst = [Instruction (Just typeId, OpTypeArray (searchTypeId' baseType) constId)]
                  inst3' = inst2{typeFields = typeFields inst2 ++ arrayInst}
               in (state4, inst3')
            DTypePointer storage DTypeVoid -> (state2, emptyInstructions)
            DTypePointer storage baseType ->
              let pointerInst = [Instruction (Just typeId, OpTypePointer storage (searchTypeId' baseType))]
                  inst2' = emptyInstructions{typeFields = pointerInst}
               in (state2, inst2')
            DTypeStruct name baseTypes ->
              let structInst = [Instruction (Just typeId, OpTypeStruct (ShowList (map searchTypeId' baseTypes)))]
                  inst2' = emptyInstructions{typeFields = structInst}
               in (state2, inst2')
            DTypeFunction returnType argTypes ->
              let functionInst = [Instruction (Just typeId, OpTypeFunction (searchTypeId' returnType) (ShowList (map (searchTypeId' . DTypePointer Function) argTypes)))]
                  inst2' = emptyInstructions{typeFields = functionInst}
               in (state2, inst2')

          updatedState =
            state3
              { idCount = idCount state3
              , idMap = idMap state3
              }
       in (updatedState, typeId, inst +++ inst3)

generateConst :: State -> Literal -> (State, OpId, Instructions)
generateConst state v =
  let dtype = case v of
        LBool _ -> DTypeBool
        LUint _ -> DTypeUInt 32
        LInt _ -> DTypeInt 32
        LFloat _ -> DTypeFloat 32
      (state', typeId, typeInst) = generateType state dtype
      (state'', ExprResult (constId, dType)) = insertResult state' (ResultConstant v) Nothing
      constInstruction = [Instruction (Just constId, OpConstant typeId v)]
      inst = typeInst{constFields = constFields typeInst ++ constInstruction}
   in (state'', constId, inst)

generateNegOp :: State -> Variable -> (State, Variable, StackInst)
generateNegOp state v =
  let id = Id (idCount state + 1)
      (e, t, typeId) = (fst v, snd v, searchTypeId state (snd v))
      state' =
        state
          { idCount = idCount state + 1
          }
      inst =
        case t of
          t
            | t == bool ->
                [Instruction (Just id, OpLogicalNot typeId e)]
            | t == int32 ->
                [Instruction (Just id, OpSNegate typeId e)]
            | t == float32 ->
                [Instruction (Just id, OpFNegate typeId e)]
          _ -> error ("not support neg of " ++ show t)
      result = (id, t)
   in (state', result, inst)

generateBinOp :: State -> Variable -> Ast.Op (Range, Type) -> Variable -> (State, Variable, Instructions, StackInst)
generateBinOp state v1 op v2 =
  let (e1, t1, typeId1) = (fst v1, snd v1, searchTypeId state (snd v1))
      (e2, t2, typeId2) = (fst v2, snd v2, searchTypeId state (snd v2))
      state' =
        state
          { idCount = idCount state + 1
          }
      id = Id (idCount state')
      (resultType, instruction) =
        case (t1, t2) of
          (t1, t2)
            | t1 == bool && t2 == bool ->
                case op of
                  Ast.Eq _ -> (bool, Instruction (Just id, OpLogicalEqual typeId1 e1 e2))
                  Ast.Neq _ -> (bool, Instruction (Just id, OpLogicalNotEqual typeId1 e1 e2))
                  Ast.And _ -> (bool, Instruction (Just id, OpLogicalAnd typeId1 e1 e2))
                  Ast.Or _ -> (bool, Instruction (Just id, OpLogicalOr typeId1 e1 e2))
            | t1 == int32 && t2 == int32 ->
                case op of
                  Ast.Plus _ -> (int32, Instruction (Just id, OpIAdd typeId1 e1 e2))
                  Ast.Minus _ -> (int32, Instruction (Just id, OpISub typeId1 e1 e2))
                  Ast.Times _ -> (int32, Instruction (Just id, OpIMul typeId1 e1 e2))
                  Ast.Divide _ -> (int32, Instruction (Just id, OpSDiv typeId1 e1 e2))
                  Ast.Eq _ -> (bool, Instruction (Just id, OpIEqual typeId1 e1 e2))
                  Ast.Neq _ -> (bool, Instruction (Just id, OpINotEqual typeId1 e1 e2))
                  Ast.Lt _ -> (bool, Instruction (Just id, OpSLessThan typeId1 e1 e2))
                  Ast.Le _ -> (bool, Instruction (Just id, OpSLessThanEqual typeId1 e1 e2))
                  Ast.Gt _ -> (bool, Instruction (Just id, OpSGreaterThan typeId1 e1 e2))
                  Ast.Ge _ -> (bool, Instruction (Just id, OpSGreaterThanEqual typeId1 e1 e2))
            | t1 == int32 && t2 == float32 -> error "Not implemented"
            | t1 == float32 && t2 == int32 -> error "Not implemented"
            | t1 == float32 && t2 == float32 ->
                case op of
                  Ast.Plus _ -> (float32, Instruction (Just id, OpFAdd typeId1 e1 e2))
                  Ast.Minus _ -> (float32, Instruction (Just id, OpFSub typeId1 e1 e2))
                  Ast.Times _ -> (float32, Instruction (Just id, OpFMul typeId1 e1 e2))
                  Ast.Divide _ -> (float32, Instruction (Just id, OpFDiv typeId1 e1 e2))
                  Ast.Eq _ -> (bool, Instruction (Just id, OpFOrdEqual typeId1 e1 e2))
                  Ast.Neq _ -> (bool, Instruction (Just id, OpFOrdNotEqual typeId1 e1 e2))
                  Ast.Lt _ -> (bool, Instruction (Just id, OpFOrdLessThan typeId1 e1 e2))
                  Ast.Le _ -> (bool, Instruction (Just id, OpFOrdLessThanEqual typeId1 e1 e2))
                  Ast.Gt _ -> (bool, Instruction (Just id, OpFOrdGreaterThan typeId1 e1 e2))
                  Ast.Ge _ -> (bool, Instruction (Just id, OpFOrdGreaterThanEqual typeId1 e1 e2))
            | t1 == t2 && (t1 == vector2 || t1 == vector3 || t1 == vector4) ->
                case op of
                  Ast.Plus _ -> (t1, Instruction (Just id, OpFAdd typeId1 e1 e2))
                  Ast.Minus _ -> (t1, Instruction (Just id, OpFSub typeId1 e1 e2))
                  Ast.Times _ -> (t1, Instruction (Just id, OpFMul typeId1 e1 e2))
            | (t1 == vector2 || t1 == vector3 || t1 == vector4) && (t2 == int32 || t2 == float32) ->
                case op of
                  Ast.Times _ -> (vector2, Instruction (Just id, OpVectorTimesScalar typeId1 e1 e2))
            | (t1 == int32 || t1 == float32) && (t2 == vector2 || t2 == vector3 || t2 == vector4) ->
                case op of
                  Ast.Times _ -> (vector2, Instruction (Just id, OpVectorTimesScalar typeId1 e1 e2))
          _ -> error ("Not implemented" ++ show t1 ++ show op ++ show t2)
   in (state', (id, resultType), emptyInstructions, [instruction])

generateExpr :: State -> Expr -> (State, ExprReturn, Instructions,VariableInst, StackInst)
generateExpr state expr =
  case expr of
    Ast.EBool _ b -> let (s,v,i,si) = handleConst state (LBool b) bool in (s, v, i, [], si)
    Ast.EInt _ int -> let (s,v,i,si) = handleConst state (LInt int) int32 in (s, v, i, [], si)
    Ast.EFloat _ f ->let (s,v,i,si) = handleConst state (LFloat f) float32 in (s, v, i, [], si)
    Ast.EList _ l ->handleArray state l
    Ast.EPar _ e -> generateExpr state e
    Ast.EVar (_, t1) (Ast.Name (_, _) name) ->let (s,v,i,si) = handleVar state t1 name in (s, v, i, [], si)
    Ast.EString _ _ -> error "String"
    Ast.EUnit _ -> error "Unit"
    Ast.EApp _ e1 e2 -> handleApp state e1 e2
    Ast.EIfThenElse _ e1 e2 e3 -> handleIfThenElse state e1 e2 e3
    Ast.ENeg _ e -> handleNeg state e
    Ast.EBinOp _ e1 op e2 -> handleBinOp state e1 op e2
    Ast.EOp _ _ -> let (s,v,i,si) = handleOp state expr in (s, v, i, [], si)
    Ast.ELetIn _ decs e -> handleLetIn state decs e

handleLetIn :: State -> [Dec] -> Expr -> (State, ExprReturn, Instructions, VariableInst, StackInst)
handleLetIn state decs e =
  let 
    (envs, envType )= env state
    state1 = state {env = (envs++["letIn"], envType)}
    (state2,  inst, varInst,stackInst) = foldl (\(s, acc, acc1,acc2) dec -> let (s', i,vi, si) = generateDec s dec in (s',  acc +++ i, acc1++vi,acc2 ++ si)) (state1,  emptyInstructions, [],[]) decs
    (state3, result, inst1,varInst2 ,stackInst1) = generateExpr state2 e

    state4 = state3 {env = (envs, envType)}
  in (state4, result, inst +++ inst1,varInst++varInst2, stackInst ++ stackInst1)
    -- in error (show (findResult state2 (ResultVariableValue (env state2, "x", envType))))
    -- in error (show (idMap state2))


handleConst :: State -> Literal -> DataType -> (State, ExprReturn, Instructions, StackInst)
handleConst state lit dType =

  let (s, id, inst) = generateConst state lit
   in (s, ExprResult (id, dType), inst,[])

handleArray :: State -> [Expr] -> (State, ExprReturn, Instructions, VariableInst, StackInst)
handleArray state l =
  let len = length l
      (state1, results, inst, var ,stackInst) =
        -- FIXME: unsure what to modify here
        foldl
          ( \(s, acc, acc1, acc2,acc3) e ->
              let (s', r, i, var ,si) = generateExpr s e in (s', acc ++ [r], acc1 +++ i,acc2 ++var ,acc3++ si)
          )
          (state, [], emptyInstructions, [],[])
          l
      -- (state2, typeId, typeInst) = generateType state1 (DTypeArray len baseTypeId)

      (state2, typeId, typeInst) = generateType state1 (DTypeArray len DTypeUnknown)
   in error "Not implemented array"

handleOp :: State -> Expr -> (State, ExprReturn, Instructions, StackInst)
handleOp state (Ast.EOp _ op) =
  let funcSign = case op of
        Ast.Plus _ -> (DTypeUnknown, [DTypeUnknown, DTypeUnknown])
        Ast.Minus _ -> (DTypeUnknown, [DTypeUnknown])
        Ast.Times _ -> (DTypeUnknown, [DTypeUnknown, DTypeUnknown])
        Ast.Divide _ -> (DTypeUnknown, [DTypeUnknown, DTypeUnknown])
        Ast.Eq _ -> (bool, [DTypeUnknown, DTypeUnknown])
        Ast.Neq _ -> (bool, [DTypeUnknown, DTypeUnknown])
        Ast.Lt _ -> (bool, [DTypeUnknown, DTypeUnknown])
        Ast.Le _ -> (bool, [DTypeUnknown, DTypeUnknown])
        Ast.Gt _ -> (bool, [DTypeUnknown, DTypeUnknown])
        Ast.Ge _ -> (bool, [DTypeUnknown, DTypeUnknown])
        Ast.And _ -> (DTypeUnknown, [DTypeUnknown, DTypeUnknown])
        Ast.Or _ -> (DTypeUnknown, [DTypeUnknown, DTypeUnknown])
   in (state, ExprApplication (OperatorFunction op) funcSign [], emptyInstructions, [])

handleVarFunction :: State -> String -> FunctionSignature -> (State, ExprReturn, Instructions,  StackInst)
handleVarFunction state name (returnType, args) =
  let result = findResult state (ResultFunction name (returnType, args))
   in case result of
        Just x -> (state, x, emptyInstructions, [])
        Nothing ->
          case (typeStringConvert name, returnType, args) of
            (Just x, return, args)
              | x == return -> (state, ExprApplication (TypeConstructor return) (return, args) [], emptyInstructions, [])
            (Nothing, return, args)
              | name == "foldl" -> (state, ExprApplication FunctionFoldl (return, args) [], emptyInstructions, [])
              | name == "map" -> (state, ExprApplication FunctionMap (return, args) [], emptyInstructions, [])
              | name == "extract_0" -> if length args == 1 && return == float32 then (state, ExprApplication (TypeExtractor returnType [0]) (return, args) [], emptyInstructions, []) else error (name ++ ":" ++ show args)
              | name == "extract_1" -> if length args == 1 && return == float32 then (state, ExprApplication (TypeExtractor returnType [1]) (return, args) [], emptyInstructions, []) else error (name ++ ":" ++ show args)
              | name == "extract_2" -> if length args == 1 && return == float32 then (state, ExprApplication (TypeExtractor returnType [2]) (return, args) [], emptyInstructions, []) else error (name ++ ":" ++ show args)
              | name == "extract_3" -> if length args == 1 && return == float32 then (state, ExprApplication (TypeExtractor returnType [3]) (return, args) [], emptyInstructions, []) else error (name ++ ":" ++ show args)
              | True ->
                  let dec = fromMaybe (error (name ++ show args)) (findDec (decs state) name Nothing)
                      (state', id, inst1) = generateFunction (state, emptyInstructions) dec
                   in -- temp =generateFunction
                      -- error (show id ++ show (functionFields inst1))
                      (state', ExprApplication (CustomFunction id name) (return, args) [], inst1, [])
            -- custom function -- cus            (Nothing, return, args) -> -- custom function -- cus            (Nothing, return, args) -> -- custom function -- cus            (Nothing, return, args) -> -- custom function
            -- case findResult state (ResultFunction name ) of {}
            _ -> error "Not implemented function"

handleVar :: State -> Type-> BS.ByteString -> (State, ExprReturn, Instructions, StackInst)
handleVar state t1 n =
  let dType = typeConvert t1
      -- (state1, typeId, typeInst) = generateType state dType
      (state3, var, inst, stackInst) = case dType of
        DTypeFunction return args ->
          -- function variable
          handleVarFunction state (BS.unpack n) (return, args)
        _ ->
          -- value variable
          let maybeResult = findResult state (ResultVariableValue (env state, BS.unpack n, dType))
           in case maybeResult of
                Just x -> (state, x, emptyInstructions, [])
                Nothing ->
                  let ExprResult (varId, varType) = fromMaybe (error ("can find var:" ++ show (env state, BS.unpack n, dType))) (findResult state (ResultVariable (env state, BS.unpack n, dType)))
                      (state2, ExprResult (valueId, _)) = insertResult state (ResultVariableValue (env state, BS.unpack n, dType)) Nothing
                      inst = [Instruction (Just valueId, OpLoad (searchTypeId state2 varType) varId)]
                   in (state2, ExprResult (valueId, varType), emptyInstructions, inst)
   in (state3, var, inst, stackInst)

handleApp :: State -> Expr -> Expr -> (State, ExprReturn, Instructions, VariableInst, StackInst)
handleApp state e1 e2 =
  let (state1, var1, inst1, varInst1,stackInst1) = generateExpr state e1
      (state2, var2, inst2, varInst2,stackInst2) = generateExpr state1 e2
      (state4, var3, inst3, varInst3,stackInst3) = case var1 of
        ExprApplication funcType (returnType, argTypes) args ->
          let args' = case var2 of
                ExprResult v -> args ++ [v] -- add argument
                _ -> error "Expected ExprResult"
              functionType = DTypeFunction returnType argTypes
           in case (length args', length argTypes) of
                (l, r) | l == r -> case funcType of
                  CustomFunction id s -> applyFunction state2 id returnType args'
                  TypeConstructor t -> let (s,v,i,si) = handleConstructor state2 t functionType args' in (s,v,i,[],si)
                  TypeExtractor t int -> let (s,v,i,si)=  handleExtract state2 t int (head args') in (s,v,i,[],si)
                  OperatorFunction op -> error "Not implemented" -- todo
                (l, r)
                  | l < r -> (state2, ExprApplication funcType (returnType, argTypes) args', emptyInstructions, [],[])
                (l, r) | l > r -> error "Too many arguments"
        _ -> error (show var1 ++ show var2)
   in (state4, var3, inst1 +++ inst2 +++ inst3, varInst1++varInst2++varInst3 ,stackInst1 ++ stackInst2 ++ stackInst3)

handleConstructor :: State -> DataType -> DataType -> [Variable] -> (State, ExprReturn, Instructions, StackInst)
handleConstructor state returnType functionType args =
  let (state1, typeId, inst) = generateType state returnType
      state2 = state1{idCount = idCount state1 + 1}
      returnId = Id (idCount state2) -- handle type convert
      stackInst = [Instruction (Just returnId, OpCompositeConstruct typeId (ShowList (map fst args)))]
   in (state2, ExprResult (returnId, returnType), inst, stackInst)

handleExtract :: State -> DataType -> [Int] -> Variable -> (State, ExprReturn, Instructions, StackInst)
handleExtract state returnType i var =
  let (state1, typeId, inst) = generateType state returnType
      state2 = state1{idCount = idCount state1 + 1}
      returnId = Id (idCount state2)
      stackInst = [Instruction (Just returnId, OpCompositeExtract typeId (fst var) (ShowList i))]
   in (state2, ExprResult (returnId, returnType), inst, stackInst)

applyFunction :: State -> OpId -> DataType -> [Variable] -> (State, ExprReturn, Instructions,VariableInst, StackInst)
applyFunction state id returnType args =
  do
    let (state1, typeIds, inst1) =
          foldr
            ( ( \t (s, acc, acc1) ->
                  let (s', id, inst) = generateType s t in (s', id : acc, inst +++ acc1)
              )
                . DTypePointer Function
                . snd
            )
            (state, [], emptyInstructions)
            args
    let (ids, vars,varInst, stackInst) =
          -- FIXME: unsure what to modify here
          foldl
            ( \(id, vars, acc,acc1) (typeId, t) ->
                let
                  varId = IdName ("param_" ++ show id)
                 in
                  ( id + 1
                  , vars ++ [(varId, t)]
                  , acc ++[Instruction (Just varId, OpVariable typeId Function)]
                  , acc1 ++ [ Instruction (Nothing, OpStore varId (fst t))]
                  )
            )
            (idCount state1 + 1, [],[], [])
            (zip typeIds args)
    let state2 = state1{idCount = ids}
    let resultId = Id (idCount state2)
    let stackInst' = stackInst ++ [Instruction (Just resultId, OpFunctionCall (searchTypeId state returnType) id (ShowList (map fst vars)))]
    -- (state', vars, typeInst, inst') = foldl (\(s, v, t, i) arg -> let (s', v', t', i') = functionPointer s arg in (s', v' : v, t ++ t', i ++ i')) (state, [], [], []) args
    -- state' = state {idCount = idCount state + 1}
    (state2, ExprResult (resultId, returnType), inst1, varInst,stackInst')

handleIfThenElse :: State -> Expr -> Expr -> Expr -> (State, ExprReturn, Instructions, VariableInst, StackInst)
handleIfThenElse state e1 e2 e3 =
  let (state1, ExprResult var1, inst1,varInst1, stackInst1) = generateExpr state e1
      (state2, var2, inst2,varInst2, stackInst2) = generateExpr state1 e2
      (state3, var3, inst3,varInst3, stackInst3) = generateExpr state2 e3
      conditionId = case var1 of
        (id, DTypeBool) -> id
        _ -> error "Expected bool"
      id = idCount state3
      sInst1' = stackInst1 ++ [Instruction (Nothing, OpBranchConditional conditionId (Id (id + 1)) (Id (id + 2)))]
      sInst2' = [Instruction (Just (Id (id + 1)), OpLabel)] ++ stackInst2 ++ [Instruction (Nothing, OpBranch (Id (id + 3)))]
      sInst3' =
        [Instruction (Just (Id (id + 2)), OpLabel)]
          ++ stackInst3
          ++ [Instruction (Nothing, OpBranch (Id (id + 3)))]
          ++ [Instruction (Just (Id (id + 3)), OpLabel)]
      state4 = state3{idCount = id + 3}
   in -- todo handle return variable
      (state3, var3, inst1 +++ inst2 +++ inst3,varInst1++varInst2++varInst3, sInst1' ++ sInst2' ++ sInst3')

-- error "Not implemented if then else"

handleNeg :: State -> Expr -> (State, ExprReturn, Instructions,VariableInst ,StackInst)
handleNeg state e =
  let (state1, ExprResult var, inst1,varInst1, stackInst1) = generateExpr state e
      (state2, var', stackInst2) = generateNegOp state1 var
   in (state2, ExprResult var', inst1,varInst1 ,stackInst1 ++ stackInst2)

handleBinOp :: State -> Expr -> Ast.Op (Range, Type) -> Expr -> (State, ExprReturn, Instructions,VariableInst, StackInst)
handleBinOp state e1 op e2 =
  let (state1, ExprResult var1, inst1,varInst1, stackInst1) = generateExpr state e1
      (state2, ExprResult var2, inst2,varInst2, stackInst2) = generateExpr state1 e2
      (state3, var3, inst3, stackInst3) = generateBinOp state2 var1 op var2
   in (state3, ExprResult var3, inst1 +++ inst2 +++ inst3,varInst1++varInst2, stackInst1 ++ stackInst2 ++ stackInst3)

generateDec :: State -> Dec -> (State, Instructions, VariableInst, StackInst)
generateDec state (Ast.DecAnno _ name t) = (state, emptyInstructions, [],[])
generateDec state (Ast.Dec (_, t) (Ast.Name (_, _) name) [] e) =
  let varType = typeConvert t
      (state1, typeId, inst1) = generateType state varType
      (state2, result, inst2,varInst, stackInst) = generateExpr state1 e
      -- (state3, _) = insertResult state2 (ResultVariable (env state2, BS.unpack name, varType)) (Just result)
      (state3, _) = insertResult state2 (ResultVariableValue (env state2, BS.unpack name, varType)) (Just result)
    in (state3, inst1 +++ inst2,varInst, stackInst)

generateInit :: Config -> [Dec] -> (State, Instructions)
generateInit h dec =
  do
    let startId = 0
    let headInstruction =
          emptyHeaderFields
            { capabilityInst = Just $ Instruction (Nothing, OpCapability (capability h))
            , extensionInst = Just $ Instruction (Just (Id (startId + 1)), OpExtInstImport (extension h))
            , memoryModelInst = Just $ Instruction (Nothing, OpMemoryModel (addressModel h) (memoryModel h))
            , -- , Instruction (Nothing, OpEntryPoint (shaderType h) (IdName (entryPoint h)) (entryPoint h) (ShowList ids))
              executionModeInst = Just $ Instruction (Nothing, OpExecutionMode (IdName (entryPoint h)) (executionMode h))
            , sourceInst = Just $ Instruction (Nothing, uncurry OpSource (source h))
            }

    -- let constInstruction = []
    let state =
          State
            { idCount = startId + 1
            , idMap = Map.empty
            , env = ([entryPoint h], DTypeVoid)
            , decs = dec
            }
    let (state1, _) = insertResult state (ResultCustom "ext ") (Just (ExprResult (Id 1, DTypeVoid))) -- ext
    let inst =
          Instructions
            { headerFields = headInstruction
            , nameFields = [Instruction (Nothing, Comment "Name fields")]
            , uniformsFields = [Instruction (Nothing, Comment "uniform fields")]
            , typeFields = [Instruction (Nothing, Comment "Type fields")]
            , constFields = [Instruction (Nothing, Comment "Const fields")]
            , functionFields = []
            }
    (state1, inst)

generateUniforms :: State -> Config -> [Argument] -> (State, Instructions)
generateUniforms state config arg =
  do
    let (_, uniforms) =
          foldr
            ( \(Ast.Argument (_, t) (Ast.Name _ name)) (i, acc) ->
                let
                  acc' = (BS.unpack name, typeConvert t, Input, i) : acc
                 in
                  (i + 1, acc')
            )
            (0, [])
            arg
    let uniforms' = ("outColor", vector4, Output, 0) : uniforms -- todo handle custom output
    let (state', inst, ids) =
          -- FIXME: unsure what to modify here
          --
          -- foldr
          --   ( \(name, dType, storage, location) (s, i, accId) ->
          --       do
          --         let (s1, typeId, inst1) = generateType s (DTypePointer storage dType)
          --         let (s2, ExprResult (id, _)) = insertResult s1 (ResultVariable (env s1, name, dType)) Nothing

          --         let variableInstruction = Instruction (Just id, OpVariable typeId storage)
          --         let nameInstruction = Instruction (Nothing, OpName id name)
          --         let uniformsInstruction = Instruction (Nothing, OpDecorate id (Location location))

          --         let inst1' =
          --               inst1
          --                 { nameFields = nameInstruction : nameFields inst1
          --                 , uniformsFields = uniformsInstruction : uniformsFields inst1
          --                 , constFields = variableInstruction : constFields inst1
          --                 }
          --         let updatedInst = inst1' +++ i

          --         (s2, updatedInst, id : accId)
          --   )
          foldl
            ( \(s, i, accId) (name, dType, storage, location) ->
                do
                  let (s1, typeId, inst1) = generateType s (DTypePointer storage dType)
                  let (s2, ExprResult (id, _)) = insertResult s1 (ResultVariable (env s1, name, dType)) Nothing

                  let variableInstruction = [Instruction (Just id, OpVariable typeId storage)]
                  let nameInstruction = [Instruction (Nothing, OpName id name)]
                  let uniformsInstruction = [Instruction (Nothing, OpDecorate id (Location location))]

                  let inst1' =
                        inst1
                          { nameFields = nameFields inst1 ++ nameInstruction
                          , uniformsFields = uniformsFields inst1 ++ uniformsInstruction
                          , constFields = constFields inst1 ++ variableInstruction
                          }
                  let updatedInst = i +++ inst1'

                  (s2, updatedInst, accId ++ [id])
            )
            (state, emptyInstructions, [])
            uniforms'
    let hf = trace "test" $ headerFields inst
    let hf' = hf{entryPointInst = Just $ Instruction (Nothing, OpEntryPoint (shaderType config) (IdName (entryPoint config)) (entryPoint config) (ShowList ids))}
    let inst1 = inst{headerFields = hf'}
    (state', inst1)

-- error (show (env state') ++ show uniforms')

generateFunctionParam :: State -> [Ast.Argument (Range, Type)] -> (State, Instructions, [Instruction])
generateFunctionParam state arg =
  do
    let vars =
          foldr
            ( \(Ast.Argument (_, t) (Ast.Name (_, _) name)) acc ->
                (BS.unpack name, typeConvert t) : acc
            )
            []
            arg
    let (state', inst, stackInst) =
          foldr
            ( \(name, dType) (s, i, stackInst) ->
                let (s', typeId, inst1) = generateType s (DTypePointer Function dType)
                    (s'', ExprResult (id, _)) = insertResult s' (ResultVariable (env s', name, dType)) Nothing
                    paramInst = Instruction (Just id, OpFunctionParameter typeId)
                 in (s'', inst1 +++ i, paramInst : stackInst)
            )
            (state, emptyInstructions, [])
            vars
    (state', inst, stackInst)

-- error (show (env state') ++ show vars)

generateFunction :: (State, Instructions) -> Dec -> (State, OpId, Instructions)
generateFunction (state, inst) (Ast.DecAnno _ name t) = (state, IdName "", inst)
generateFunction (state, inst) (Ast.Dec (_, t) (Ast.Name (_, _) name) args e) =
  do
    let DTypeFunction returnType argsType = typeConvert t
    let functionType = DTypeFunction returnType argsType
    let (state1, typeId, inst1) = generateType state functionType

    let state2 = state1{env = ([BS.unpack name], functionType)}

    let (state3, ExprResult (funcId, funcType)) = insertResult state2 (ResultFunction (BS.unpack name) (returnType, argsType)) Nothing
    let (state4, inst2, paramInst) = generateFunctionParam state3 args
    let state5 = state4{idCount = idCount state4 + 1}
    let labelId = Id (idCount state5)
    let (state6, ExprResult (resultId, _), inst3,varInst, exprInst) = generateExpr state5 e  -- todo handle return variable are function
    let state7 = state6{env = env state}
    let returnTypeId = searchTypeId state7 returnType

    let funcInst = FunctionInst {
      begin = [Instruction (Nothing, Comment ("function " ++ BS.unpack name)), Instruction (Just funcId, OpFunction returnTypeId None typeId)],
      parameter = paramInst,
      label = [Instruction (Just labelId, OpLabel)],
      variable = varInst,
      body = exprInst ++ [Instruction (Nothing, OpReturnValue resultId)],
      end = [Instruction (Nothing, OpFunctionEnd)]
    }
    let inst4 = inst +++ inst1 +++ inst2 +++ inst3

    let inst5 = inst4{functionFields = functionFields inst4 ++ [funcInst]}
    -- (state'''', ExprResult var, typeInst, inst') = generateExpr state''' e
    (state7, funcId, inst5)

generateMainFunction :: (State, Instructions) -> Config -> Dec -> (State, Instructions)
generateMainFunction (state, inst) config (Ast.Dec (_, t) (Ast.Name (_, _) name) args e) =
  do
    let (returnType, argsType) = (DTypeVoid, [])
    let functionType = DTypeFunction returnType argsType
    let (state1, typeId, inst1) = generateType state functionType
    let (state2, ExprResult (funcId, _)) = insertResult state1 (ResultCustom "func ") (Just (ExprResult (IdName (BS.unpack name), functionType)))

    let state3 = state2{idCount = idCount state2 + 1, env = ([BS.unpack name], functionType)}
    let labelId = Id (idCount state3)

    let (state4, inst2) = generateUniforms state3 config args
    let (state5, ExprResult (resultId, _), inst3,varInst ,exprInst) = generateExpr state4 e
    let returnTypeId = searchTypeId state5 returnType

    -- ExprResult (varId, _) = fromMaybe (error "cant find var :outColor") (findResult state5 (ResultVariableValue (env state5, "outColor", vector4)))
    let ExprResult (varId, _) = fromMaybe (error (show (env state5))) (findResult state5 (ResultVariable (env state5, "outColor", vector4)))
    let saveInst = [Instruction (Nothing, OpStore varId resultId)]

    let funcInst = FunctionInst {
      begin = [Instruction (Nothing, Comment ("function " ++ BS.unpack name)), Instruction (Just funcId, OpFunction returnTypeId None typeId)],
      parameter = [],
      label = [Instruction (Just labelId, OpLabel)],
      variable = varInst,
      body = exprInst ++ [Instruction (Nothing, OpReturn)],
      end = [Instruction (Nothing, OpFunctionEnd)]
    }

    let inst4 = inst +++ inst1 +++ inst2 +++ inst3
    let inst5 = inst4{functionFields = functionFields inst4 ++ [funcInst]}
    (state5, inst5)

-- search dec by name and function signature
findDec :: [Dec] -> String -> Maybe FunctionSignature -> Maybe Dec
findDec decs name Nothing =
  let
    aux =
      ( \case
          Ast.Dec _ (Ast.Name _ n) _ _ -> n == BS.pack name
          _ -> False
      )
   in
    case filter aux decs of
      [d] -> Just d
      _ -> Nothing
findDec decs name (Just (returnType, args)) =
  let
    aux =
      ( \case
          Ast.Dec _ (Ast.Name _ n) args' _ ->
            let args'' = map (\(Ast.Argument (_, t) _) -> typeConvert t) args'
             in n == BS.pack name && args'' == args
          _ -> False
      )
   in
    case filter aux decs of
      [d] -> Just d
      _ -> Nothing
flattenFunctionInst :: FunctionInst -> [Instruction]
flattenFunctionInst func =
  do
    let FunctionInst {begin, parameter, label, variable, body, end} = func
    begin ++ parameter ++ label ++ variable ++ body ++ end

instructionsToString :: Instructions -> String
instructionsToString inst =
  do
    let code =
          fromHeaderFields (headerFields inst)
            ++ nameFields inst
            ++ uniformsFields inst
            ++ typeFields inst
            ++ constFields inst
            ++ concatMap flattenFunctionInst (functionFields inst)
    let codeText = intercalate "\n" (map show code)
    codeText

generate :: Config -> [Dec] -> Instructions
generate config decs =
  do
    let init@(initState, inst) = generateInit config decs
    let mainDec = findDec decs (entryPoint config) Nothing
    let (state', inst') = generateMainFunction init config (fromJust mainDec)
    -- (state3, _, inst2) = generateType initState (DTypePointer Input vector2)
    let finalInst = inst'
    finalInst

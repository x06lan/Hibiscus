{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-missing-signatures #-}

module Hibiscus.CodeGen where

-- import qualified Data.Set as Set

import Control.Applicative (Alternative (empty))
import Control.Exception (handle)
import Data.ByteString (cons)
import qualified Data.ByteString.Lazy.Char8 as BS
import Data.Data (Data)
import Data.Functor.Classes (readsUnary)
import Data.List (find, intercalate)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import GHC.ExecutionStack (showStackTrace)
import Hibiscus.Asm
import Hibiscus.Ast (Dec)
import qualified Hibiscus.Ast as Ast
import Hibiscus.Lexer
import Hibiscus.Parser
import Hibiscus.Type
import Hibiscus.Typing

-- import Data.IntMap (fromList, foldlWithKey)

type Variable = (OpId, DataType)

type Uniform = (String, DataType, StorageClass, Int)

type DecType = Ast.Dec (Range, Ast.Type Range)

type FunctionSignature = (DataType, [DataType]) -- return type, arguments

type Env = (String, DataType) -- function name, function type

type ResultMap = Map.Map ResultType ExprReturn

data Config = Config
  { capability :: Capability,
    extension :: String,
    memoryModel :: MemoryModel,
    addressModel :: AddressingModel,
    executionMode :: ExecutionMode,
    shaderType :: ExecutionModel,
    source :: (SourceLanguage, Int),
    entryPoint :: String,
    uniforms :: [Uniform] -- (name, type, position)
  }

data FunctionType
  = CustomFunction OpId String
  | TypeConstructor DataType -- function type constructor
  | TypeExtractor DataType Int -- function type decorator
  | OperatorFunction (Ast.Op (Range, Ast.Type Range))
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
    decs :: [Ast.Dec (Range, Ast.Type Range)]
  }
  deriving (Show)

data Instructions = Instructions
  { headerFields :: [Instruction],
    nameFields :: [Instruction],
    uniformsFields :: [Instruction],
    typeFields :: [Instruction],
    constFields :: [Instruction],
    functionFields :: [[Instruction]] -- [function]
  }
  deriving (Show)

(+++) :: Instructions -> Instructions -> Instructions
(Instructions h1 n1 u1 t1 c1 f1) +++ (Instructions h2 n2 u2 t2 c2 f2) =
  Instructions (h1 ++ h2) (n1 ++ n2) (u1 ++ u2) (t1 ++ t2) (c1 ++ c2) (f1 ++ f2)

defaultConfig :: Config
defaultConfig =
  Config
    { capability = Shader,
      addressModel = Logical,
      memoryModel = GLSL450,
      source = (GLSL, 450),
      shaderType = Fragment,
      executionMode = OriginUpperLeft,
      extension = "GLSL.std.450",
      entryPoint = "main",
      uniforms = [("uv", vector2, Input, 0), ("outColor", vector4, Output, 0)]
    }

emptyInstructions :: Instructions
emptyInstructions =
  Instructions
    { headerFields = [],
      nameFields = [],
      uniformsFields = [],
      typeFields = [],
      constFields = [],
      functionFields = []
    }

findResult :: State -> ResultType -> Maybe ExprReturn
findResult s key = Map.lookup key (idMap s)

insertResult :: State -> ResultType -> Maybe ExprReturn -> (State, ExprReturn)
insertResult state key Nothing =
  case findResult state key of
    Just existingResult -> (state, existingResult)
    Nothing ->
      let (newMap, newId, newCount) = generateEntry state key
          updatedState = state {idMap = newMap, idCount = newCount}
       in (updatedState, newId)
-- error (show key ++ " not found")
insertResult state key (Just value) =
  case findResult state key of
    Just existingResult -> (state, existingResult)
    Nothing ->
      let newMap = Map.insert key value (idMap state)
          updatedState = state {idMap = newMap}
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
                LBool b -> (IdName ("bool" ++ show b), DTypeBool)
                LUint i -> (IdName ("uint" ++ show i), uint32)
                LInt i -> (IdName ("int" ++ show i), int32)
                LFloat f -> (IdName ("float" ++ map (\c -> if c == '.' then '_' else c) (show f)), float32)
              result = ExprResult var
           in (Map.insert key result currentMap, result, currentCount)
        ResultVariable ((envName, envType), s, varType) ->
          let var = (IdName (envName ++ "_" ++ s), varType)
              result = ExprResult var
           in (Map.insert key result currentMap, result, currentCount)
        ResultVariableValue ((envName, envType), s, varType) ->
          let var = (Id (currentCount + 1), varType)
              result = ExprResult var
           in (Map.insert key result currentMap, result, currentCount + 1)
        ResultFunction s (return, args) ->
          let t = DTypeFunction return args
              var = (IdName (intercalate "_" (s : (map show args))), t)
              result = ExprResult var
           in (Map.insert key result currentMap, result, currentCount)

searchTypeId :: State -> DataType -> OpId
searchTypeId s dt = case findResult s (ResultDataType dt) of
  Just x -> case x of
    ExprResult (id, _) -> id
    _ -> error (show dt ++ " type not found")
  Nothing -> error (show dt ++ " type not found")

generateType :: State -> DataType -> (State, OpId, [Instruction])
generateType state dType =
  case findResult state (ResultDataType dType) of
    Just (ExprResult (typeId, _)) -> (state, typeId, [])
    Nothing ->
      let (state1, instruction) = case dType of
            DTypeUnknown -> error "Unknown type"
            DTypeVoid -> (state, [])
            DTypeBool -> (state, [])
            DTypeInt _ _ -> (state, [])
            DTypeFloat _ -> (state, [])
            DTypeVector _ baseType -> let (s', id, instrs) = generateType state baseType in (s', instrs)
            DTypeMatrix _ baseType -> let (s', id, instrs) = generateType state baseType in (s', instrs)
            DTypeArray _ baseType -> let (s', id, instrs) = generateType state baseType in (s', instrs)
            DTypePointer _ baseType -> let (s', id, instrs) = generateType state baseType in (s', instrs)
            DTypeStruct _ fields -> foldl (\(s, instrs) field -> let (s', id, instrs') = generateType s field in (s', instrs ++ instrs')) (state, []) fields
            DTypeFunction returnType argsType -> foldl (\(s, instrs) t -> let (s', id, instrs') = generateType s (DTypePointer Function t) in (s', instrs ++ instrs')) (state, []) (returnType : argsType)
          (state2, ExprResult (typeId, _)) = insertResult state1 (ResultDataType dType) Nothing
          searchTypeId' = searchTypeId state2

          typeInstruction =
            [ Instruction
                ( Just typeId,
                  case dType of
                    DTypeVoid -> OpTypeVoid
                    DTypeBool -> OpTypeBool
                    DTypeInt size sign -> OpTypeInt size sign
                    DTypeFloat size -> OpTypeFloat size
                    DTypeVector size baseType ->
                      OpTypeVector (searchTypeId' baseType) size
                    DTypeMatrix col baseType ->
                      OpTypeMatrix (searchTypeId' baseType) col
                    DTypeArray size baseType ->
                      OpTypeArray (searchTypeId' baseType) size
                    DTypePointer storage baseType ->
                      OpTypePointer (searchTypeId' baseType) storage
                    DTypeStruct name baseTypes ->
                      OpTypeStruct (ShowList (map searchTypeId' baseTypes))
                    DTypeFunction returnType argTypes ->
                      OpTypeFunction (searchTypeId' returnType) (ShowList (map (searchTypeId' . DTypePointer Function) argTypes))
                )
            ]
          updatedState =
            state2
              { idCount = idCount state2,
                idMap = idMap state2
              }
       in (updatedState, typeId, instruction ++ typeInstruction)

generateConst :: State -> Literal -> (State, OpId, Instructions)
generateConst state v =
  let dtype = case v of
        LBool _ -> DTypeBool
        LUint _ -> DTypeInt 32 0
        LInt _ -> DTypeInt 32 1
        LFloat _ -> DTypeFloat 32
      (state', typeId, typeInstruction) = generateType state dtype
      (state'', ExprResult (constId, dType)) = insertResult state' (ResultConstant v) Nothing
      constInstruction = [Instruction (Just constId, OpConstant typeId v)]
      inst = emptyInstructions {constFields = constInstruction, typeFields = typeInstruction}
   in (state'', constId, inst)

generateInit :: Config -> [DecType] -> (State, Instructions)
generateInit h dec =
  (state1, inst)
  where
    startId = 0
    headInstruction =
      [ Instruction (Nothing, OpCapability (capability h)),
        Instruction (Just (Id (startId + 1)), OpExtInstImport (extension h)),
        Instruction (Nothing, OpMemoryModel (addressModel h) (memoryModel h)),
        Instruction (Nothing, OpEntryPoint (shaderType h) (IdName (entryPoint h)) (entryPoint h) (ShowList (map (\(name, _, _, _) -> IdName name) (uniforms h)))),
        Instruction (Nothing, OpExecutionMode (IdName (entryPoint h)) (executionMode h)),
        Instruction (Nothing, OpSource (fst (source h)) (snd (source h)))
      ]

    constInstruction = []
    state =
      State
        { idCount = startId + 1,
          idMap = Map.empty,
          env = (entryPoint h, DTypeVoid),
          decs = dec
        }
    (state1, _) = insertResult state (ResultCustom ("ext ")) (Just (ExprResult (Id 1, DTypeVoid))) -- ext
    inst =
      Instructions
        { headerFields = [Instruction (Nothing, Comment "header fields")] ++ headInstruction,
          nameFields = [Instruction (Nothing, Comment "Name fields")],
          uniformsFields = [Instruction (Nothing, Comment "uniform fields")],
          typeFields = [Instruction (Nothing, Comment "Type fields")],
          constFields = [Instruction (Nothing, Comment "Const fields")],
          functionFields = [[Instruction (Nothing, Comment "functions fields")]]
        }

generateNegOp :: State -> Variable -> (State, Variable, [Instruction])
generateNegOp state v =
  let id = Id ((idCount state) + 1)
      (e, t, typeId) = (fst v, snd v, searchTypeId state (snd v))
      state' =
        state
          { idCount = idCount state + 1
          }
      inst =
        case t of
          bool ->
            [Instruction (Just id, OpLogicalNot typeId e)]
          int32 ->
            [Instruction (Just id, OpSNegate typeId e)]
          float32 ->
            [Instruction (Just id, OpFNegate typeId e)]
      result = (id, t)
   in (state', result, inst)

generateBinOp :: State -> Variable -> Ast.Op (Range, Ast.Type Range) -> Variable -> (State, Variable, Instructions, [Instruction])
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
          (t1, t2) | t1 == bool && t2 == bool ->
            case op of
              Ast.Eq _ -> (bool, Instruction (Just id, OpLogicalEqual typeId1 e1 e2))
              Ast.Neq _ -> (bool, Instruction (Just id, OpLogicalNotEqual typeId1 e1 e2))
              Ast.And _ -> (bool, Instruction (Just id, OpLogicalAnd typeId1 e1 e2))
              Ast.Or _ -> (bool, Instruction (Just id, OpLogicalOr typeId1 e1 e2))
              _ -> error ("Not implemented" ++ show t1 ++ show op ++ show t2)
          (t1, t2) | t1 == int32 && t2 == int32 ->
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
              _ -> error ("Not implemented" ++ show t1 ++ show op ++ show t2)
          (t1, t2) | t1 == int32 && t2 == float32 -> error "Not implemented"
          (t1, t2) | t1 == float32 && t2 == int32 -> error "Not implemented"
          (t1, t2) | t1 == float32 && t2 == float32 ->
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
          (t1, t2) | t1 == t2 && (t1 == vector2 || t1 == vector3 || t1 == vector4) ->
            case op of
              Ast.Plus _ -> (t1, Instruction (Just id, OpFAdd typeId1 e1 e2))
              Ast.Minus _ -> (t1, Instruction (Just id, OpFSub typeId1 e1 e2))
              Ast.Times _ -> (t1, Instruction (Just id, OpFMul typeId1 e1 e2))
          (t1, t2) | (t1 == vector2 || t1 == vector3 || t1 == vector4) && (t2 == int32 || t2 == float32) ->
            case op of
              Ast.Times _ -> (vector2, Instruction (Just id, OpVectorTimesScalar typeId1 e1 e2))
              _ -> error ("Not implemented" ++ show t1 ++ show op ++ show t2)
          (t1, t2) | (t1 == int32 || t1 == float32) && (t2 == vector2 || t2 == vector3 || t2 == vector4) ->
            case op of
              Ast.Times _ -> (vector2, Instruction (Just id, OpVectorTimesScalar typeId1 e1 e2))
              _ -> error ("Not implemented" ++ show t1 ++ show op ++ show t2)
          _ -> error ("Not implemented" ++ show t1 ++ show op ++ show t2)
      inst = [instruction]
      result = (id, resultType)
   in (state', result, emptyInstructions, inst)

generateExpr :: State -> Ast.Expr (Range, Ast.Type Range) -> (State, ExprReturn, Instructions, [Instruction])
generateExpr state expr =
  case expr of
    Ast.EBool _ b -> handleConst state (LBool b) bool
    Ast.EInt _ i -> handleConst state (LInt i) int32
    Ast.EFloat _ f -> handleConst state (LFloat f) float32
    Ast.EList _ l -> error "List"
    Ast.EPar _ e -> generateExpr state e
    Ast.EVar (_, t1) (Ast.Name (_, _) n) -> handleVar state t1 n
    Ast.EString _ _ -> error "String"
    Ast.EUnit _ -> error "Unit"
    Ast.EApp _ e1 e2 -> handleApp state e1 e2
    Ast.EIfThenElse _ e1 e2 e3 -> handleIfThenElse state e1 e2 e3
    Ast.ENeg _ e -> handleNeg state e
    Ast.EBinOp _ e1 op e2 -> handleBinOp state e1 op e2
    Ast.EOp _ _ -> handleOp state expr
    Ast.ELetIn _ _ _ -> error "LetIn"

handleConst :: State -> Literal -> DataType -> (State, ExprReturn, Instructions, [Instruction])
handleConst state lit dType =
  let (s, id, inst) = generateConst state lit
   in (s, ExprResult (id, dType), inst, [])

handleList :: State -> [Ast.Expr (Range, Ast.Type Range)] -> ExprReturn -> (State, ExprReturn, Instructions)
handleList state l returnVar =
  let len = length l
   in error "Not implemented array"

handleOp :: State -> Ast.Expr (Range, Ast.Type Range) -> (State, ExprReturn, Instructions, [Instruction])
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

handleVarFunction :: State -> String -> FunctionSignature -> (State, ExprReturn, Instructions, [Instruction])
handleVarFunction state name (returnType, args) =
  let result = findResult state (ResultFunction name (returnType, args))
   in case result of
        Just x -> (state, x, emptyInstructions, [])
        Nothing ->
          case (typeStringConvert name, returnType, args) of
            (Just x, return, args)
              | (x == return) -> (state, ExprApplication (TypeConstructor return) (return, args) [], emptyInstructions, [])
            (Nothing, return, args)
              | (name == "foldl") -> (state, ExprApplication FunctionFoldl (return, args) [], emptyInstructions, [])
              | (name == "map") -> (state, ExprApplication FunctionMap (return, args) [], emptyInstructions, [])
              | True ->
                  let dec = fromMaybe (error (name ++ show args)) (findDec (decs state) name Nothing)
                      (state', id, inst1) = generateFunction (state, emptyInstructions) dec
                   in -- temp =generateFunction
                      -- error (show id ++ show inst1)
                      (state', ExprApplication (CustomFunction id name) (return, args) [], inst1, [])
            -- custom function -- cus            (Nothing, return, args) -> -- custom function -- cus            (Nothing, return, args) -> -- custom function -- cus            (Nothing, return, args) -> -- custom function
            -- case findResult state (ResultFunction name ) of {}
            _ -> error "Not implemented function"

handleVar :: State -> Ast.Type Range -> BS.ByteString -> (State, ExprReturn, Instructions, [Instruction])
handleVar state t1 n =
  let dType = typeConvert t1
      (state1, typeId, typeInst) = generateType state dType
      (state3, var, insts, stackInst) = case dType of
        DTypeFunction return args ->
          -- function variable
          handleVarFunction state1 (BS.unpack n) (return, args)
        _ ->
          -- value variable
          let maybeResult = findResult state1 (ResultVariableValue (env state1, BS.unpack n, dType))
           in case maybeResult of
                Just x -> (state1, x, emptyInstructions, [])
                Nothing ->
                  let ExprResult (varId, varType) = fromMaybe (error ("can find var:" ++ show (env state1, BS.unpack n, dType))) (findResult state1 (ResultVariable (env state1, BS.unpack n, dType)))
                      -- inst = [Instruction (Just varId, OpVariable typeId Function)]
                      (state2, ExprResult (valueId, _)) = insertResult state1 (ResultVariableValue (env state1, BS.unpack n, dType)) Nothing
                      inst = [Instruction (Just valueId, OpLoad typeId varId)]
                   in (state2, ExprResult (valueId, varType), emptyInstructions, inst)
      inst' = insts {typeFields = typeFields insts ++ typeInst}
   in (state3, var, inst', stackInst)

handleApp :: State -> Ast.Expr (Range, Ast.Type Range) -> Ast.Expr (Range, Ast.Type Range) -> (State, ExprReturn, Instructions, [Instruction])
handleApp state e1 e2 =
  let (state1, var1, inst1, stackInst1) = generateExpr state e1
      (state2, var2, inst2, stackInst2) = generateExpr state1 e2
      (state4, var3, inst3, stackInst3) = case var1 of
        -- ExprApplication funcId (DTypeFunction returnType argTypes) args ->
        ExprApplication funcType (returnType, argTypes) args ->
          let args' = case var2 of
                ExprResult v -> args ++ [v] -- add argument
                _ -> error "Expected ExprResult"
              functionType = DTypeFunction returnType argTypes
           in case (length args', length argTypes) of
                (l, r) | l == r -> case funcType of
                  CustomFunction id s -> applyFunction state2 id returnType args'
                  TypeConstructor t -> handleConstructor state2 t functionType args'
                  TypeExtractor t i -> error "Not implemented" -- todo
                  OperatorFunction op -> error "Not implemented" -- todo
                (l, r)
                  | l < r -> (state2, ExprApplication funcType (returnType, argTypes) args', emptyInstructions, [])
                (l, r) | l > r -> error "Too many arguments"
        _ -> error (show var1)
   in (state4, var3, inst1 +++ inst2 +++ inst3, stackInst1 ++ stackInst2 ++ stackInst3)

handleConstructor :: State -> DataType -> DataType -> [Variable] -> (State, ExprReturn, Instructions, [Instruction])
handleConstructor state returnType functionType args =
  let (state1, typeId, typeInst) = generateType state returnType
      state2 = state1 {idCount = idCount state1 + 1}
      returnId = Id (idCount state2)
      stackInst = [Instruction (Just returnId, OpCompositeConstruct typeId (ShowList (map fst args)))]
      inst = emptyInstructions {typeFields = typeInst}
   in (state2, ExprResult (returnId, returnType), inst, stackInst)

-- error "Not implemented function pointer"

-- (state', ExprResult (returnId, returnType), [], inst)
applyFunction :: State -> OpId -> DataType -> [Variable] -> (State, ExprReturn, Instructions, [Instruction])
applyFunction state id returnType args =
  let (state1, typeIds, typeInst) = foldl (\(s, acc, acc1) t -> let (s', id, inst) = generateType s t in (s', acc ++ [id], acc1 ++ inst)) (state, [], []) (map (DTypePointer Function . snd) args)
      (ids, vars, stackInst) =
        foldl
          ( \(id, vars, acc) (typeId, t) ->
              let varId = IdName ("param_" ++ show id)
               in ( id + 1,
                    vars ++ [(varId, t)],
                    acc
                      ++ [ Instruction (Just varId, OpVariable typeId Function),
                           Instruction (Nothing, OpStore varId (fst t))
                         ]
                  )
          )
          (idCount state1 + 1, [], [])
          (zip typeIds args)
      state2 = state1 {idCount = ids}
      resultId = Id (idCount state2)
      stackInst' = stackInst ++ [Instruction (Just resultId, OpFunctionCall (searchTypeId state returnType) id (ShowList (map fst vars)))]
      inst = emptyInstructions {typeFields = typeInst}
   in -- (state', vars, typeInst, inst') = foldl (\(s, v, t, i) arg -> let (s', v', t', i') = functionPointer s arg in (s', v' : v, t ++ t', i ++ i')) (state, [], [], []) args
      -- state' = state {idCount = idCount state + 1}
      (state2, ExprResult (resultId, returnType), inst, stackInst')

handleIfThenElse :: State -> Ast.Expr (Range, Ast.Type Range) -> Ast.Expr (Range, Ast.Type Range) -> Ast.Expr (Range, Ast.Type Range) -> (State, ExprReturn, Instructions, [Instruction])
handleIfThenElse state e1 e2 e3 =
  let (state1, ExprResult var1, inst1, stackInst1) = generateExpr state e1
      (state2, var2, inst2, stackInst2) = generateExpr state1 e2
      (state3, var3, inst3, stackInst3) = generateExpr state2 e3
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
      state4 = state3 {idCount = id + 3}
   in -- todo handle return variable
      (state3, var3, inst1 +++ inst2 +++ inst3, sInst1' ++ sInst2' ++ sInst3')

-- error "Not implemented if then else"

handleNeg :: State -> Ast.Expr (Range, Ast.Type Range) -> (State, ExprReturn, Instructions, [Instruction])
handleNeg state e =
  let (state1, ExprResult var, inst1, stackInst1) = generateExpr state e
      (state2, var', stackInst2) = generateNegOp state1 var
   in (state2, ExprResult var', inst1, stackInst1 ++ stackInst2)

handleBinOp :: State -> Ast.Expr (Range, Ast.Type Range) -> Ast.Op (Range, Ast.Type Range) -> Ast.Expr (Range, Ast.Type Range) -> (State, ExprReturn, Instructions, [Instruction])
handleBinOp state e1 op e2 =
  let (state1, ExprResult var1, inst1, stackInst1) = generateExpr state e1
      (state2, ExprResult var2, inst2, stackInst2) = generateExpr state1 e2
      (state3, var3, inst3, stackInst3) = generateBinOp state2 var1 op var2
   in (state3, ExprResult var3, inst1 +++ inst2 +++ inst3, stackInst1 ++ stackInst2 ++ stackInst3)

generateUniforms :: State -> [Ast.Argument (Range, Ast.Type Range)] -> (State, Instructions)
generateUniforms state arg =
  let (_, uniforms) = foldl (\(i, acc) (Ast.Argument (_, t) (Ast.Name (_, _) name)) -> let acc' = acc ++ [(BS.unpack name, typeConvert t, Input, i)] in (i + 1, acc')) (0, []) arg
      uniforms' = uniforms ++ [("outColor", vector4, Output, 0)] -- todo handle custom output
      (state', inst') =
        foldl
          ( \(s, i) (name, dType, storage, location) ->
              let (s1, typeId, typeInstructions) = generateType s (DTypePointer storage dType)
                  (s2, ExprResult (id, _)) = insertResult s1 (ResultVariable (env s1, name, dType)) Nothing

                  variableInstruction = [Instruction (Just id, OpVariable typeId storage)]
                  nameInstruction = [Instruction (Nothing, OpName id name)]
                  uniformsInstruction = [Instruction (Nothing, OpDecorate id (Location location))]
                  updatedInst =
                    i
                      { nameFields = nameFields i ++ nameInstruction,
                        uniformsFields = uniformsFields i ++ uniformsInstruction,
                        constFields = constFields i ++ variableInstruction,
                        typeFields = typeFields i ++ typeInstructions
                      }
               in (s2, updatedInst)
          )
          (state, emptyInstructions)
          uniforms'
   in (state', inst')

-- error (show (env state') ++ show uniforms')

generateFunctionParam :: State -> [Ast.Argument (Range, Ast.Type Range)] -> (State, Instructions, [Instruction])
generateFunctionParam state arg =
  let vars = foldl (\acc (Ast.Argument (_, t) (Ast.Name (_, _) name)) -> acc ++ [(BS.unpack name, typeConvert t)]) [] arg
      (state', inst, stackInst) =
        foldl
          ( \(s, i, stackInst) (name, dType) ->
              let (s', typeId, typeInst) = generateType s dType
                  (s'', ExprResult (id, _)) = insertResult s' (ResultVariable (env s', name, dType)) Nothing
                  paramInst = [Instruction (Just id, OpFunctionParameter typeId)]
                  updatedInst = i {typeFields = typeFields i ++ typeInst}
               in (s'', updatedInst, stackInst ++ paramInst)
          )
          (state, emptyInstructions, [])
          vars
   in (state', inst, stackInst)

-- error (show (env state') ++ show vars)

generateFunction :: (State, Instructions) -> DecType -> (State, OpId, Instructions)
generateFunction (state, inst) (Ast.DecAnno _ name t) = (state, IdName "", inst)
generateFunction (state, inst) (Ast.Dec (_, t) (Ast.Name (_, _) name) args e) =
  let DTypeFunction returnType argsType = typeConvert t
      functionType = DTypeFunction returnType argsType
      (state1, typeId, typeInstructions) = generateType state functionType

      state2 = state1 {env = (BS.unpack name, functionType)}

      (state3, ExprResult (funcId, funcType)) = insertResult state2 (ResultFunction (BS.unpack name) (returnType, argsType)) Nothing
      (state4, inst1, paramInst) = generateFunctionParam state3 args
      (state5, ExprResult (resultId, _), inst2, exprInst) = generateExpr state4 e
      state6 = state5 {env = env state}
      returnTypeId = searchTypeId state3 returnType

      funcInst =
        [Instruction (Nothing, Comment ("function " ++ BS.unpack name))]
          ++ [Instruction (Just funcId, OpFunction returnTypeId None typeId)]
          ++ paramInst
          ++ exprInst
          ++ [Instruction (Nothing, OpReturnValue resultId)]
          ++ [Instruction (Nothing, OpFunctionEnd)]
      inst3 = inst +++ inst1 +++ inst2
      inst4 =
        inst3
          { typeFields = typeFields inst3 ++ typeInstructions,
            functionFields = functionFields inst3 ++ [funcInst]
          }
   in -- (state'''', ExprResult var, typeInst, inst') = generateExpr state''' e
      (state6, funcId, inst4)

generateMainFunction :: (State, Instructions) -> [Uniform] -> DecType -> (State, Instructions)
generateMainFunction (state, inst) uniforms (Ast.Dec (_, t) (Ast.Name (_, _) name) args e) =
  let (returnType, argsType) = (DTypeVoid, [])
      functionType = DTypeFunction returnType argsType
      (state1, typeId, typeInst) = generateType state functionType
      (state2, ExprResult (funcId, _)) = insertResult state1 (ResultCustom "func ") (Just (ExprResult (IdName (BS.unpack name), functionType)))

      state3 = state2 {env = (BS.unpack name, functionType)}
      (state4, inst1) = generateUniforms state3 args
      (state5, ExprResult var, inst2, exprInst) = generateExpr state4 e
      returnTypeId = searchTypeId state5 returnType

      funcInst =
        [Instruction (Nothing, Comment "function main")]
          ++ [Instruction (Just funcId, OpFunction returnTypeId None typeId)]
          ++ exprInst
          ++ [ Instruction (Nothing, OpReturn),
               Instruction (Nothing, OpFunctionEnd)
             ]

      inst3 = (inst +++ inst1 +++ inst2)
      inst4 =
        inst3
          { typeFields = typeFields inst3 ++ typeInst,
            functionFields = functionFields inst3 ++ [funcInst]
          }
   in (state5, inst4)

-- search dec by name and function signature
findDec :: [DecType] -> String -> Maybe FunctionSignature -> Maybe DecType
findDec decs name Nothing =
  case filter (\d -> case d of Ast.Dec (_, _) (Ast.Name (_, _) n) _ _ -> n == BS.pack name; _ -> False) decs of
    [d] -> Just d
    _ -> Nothing
findDec decs name (Just (returnType, args)) =
  case filter
    ( \d -> case d of
        Ast.Dec (_, _) (Ast.Name (_, _) n) args' _ ->
          let args'' = map (\(Ast.Argument (_, t) _) -> typeConvert t) args'
           in n == BS.pack name && args'' == args
        _ -> False
    )
    decs of
    [d] -> Just d
    _ -> Nothing

instructionsToString :: Instructions -> String
instructionsToString inst =
  let code = headerFields inst ++ nameFields inst ++ uniformsFields inst ++ typeFields inst ++ constFields inst ++ concat (functionFields inst)
      codeText = intercalate "\n" (map show code)
   in codeText

generate :: Config -> [DecType] -> Instructions
generate config decs =
  let init = generateInit config decs
      (initState, inst) = init
      mainDec = findDec decs (entryPoint config) Nothing
      (state', inst') = generateMainFunction (initState, inst) (uniforms config) (fromMaybe (error "") mainDec)
      finalInst = inst'
   in finalInst

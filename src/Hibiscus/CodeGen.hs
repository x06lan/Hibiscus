{-# LANGUAGE CPP       #-}
{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-missing-signatures #-}

module Hibiscus.CodeGen where

-- import qualified Data.Set as Set

import qualified Data.ByteString.Lazy.Char8 as BS
import           Data.Fixed                 (Uni)
import           Data.List                  (intercalate)
import qualified Data.Map                   as Map
import           Data.Maybe                 (fromMaybe)
import           Hibiscus.Asm
import           Hibiscus.Ast               (Dec)
import qualified Hibiscus.Ast               as Ast
import           Hibiscus.Lexer
import           Hibiscus.Parser
import           Hibiscus.Type
import           Hibiscus.Typing
import           Hibiscus.Typing            (DataType (DTypeFunction, DTypeVoid))

-- import Data.IntMap (fromList, foldlWithKey)

type Variable = (OpId, DataType)

type Uniform = (String, DataType, StorageClass, Int)

type DecType = Ast.Dec (Range, Ast.Type Range)

data Config = Dict
  { capability    :: Capability,
    extension     :: String,
    memoryModel   :: MemoryModel,
    addressModel  :: AddressingModel,
    executionMode :: ExecutionMode,
    shaderType    :: ExecutionModel,
    source        :: (SourceLanguage, Int),
    entryPoint    :: String,
    uniforms      :: [Uniform] -- (name, type, position)
  }

type OpIdMap = Map.Map String OpId

type Env = (String, DataType) -- function name, function type

data Instructions = Instructions
  { headerFields   :: [Instruction],
    nameFields     :: [Instruction],
    uniformsFields :: [Instruction],
    constFields    :: [Instruction],
    functionFields :: [[Instruction]] -- [function]
  }
  deriving (Show)

data State = State
  { idCount :: Int,
    idMap   :: OpIdMap,
    env     :: Env,
    decs    :: [Ast.Dec (Range, Ast.Type Range)]
  }
  deriving (Show)
data ExprReturn
  = ExprResult Variable
  | ExprApplication (Either DataType OpId) DataType [Variable] -- name function, arguments
  deriving (Show)

typeStringConvert :: BS.ByteString -> Maybe DataType
typeStringConvert t = case t of
  "Int"   -> Just int32
  "Float" -> Just float32
  "Bool"  -> Just bool
  "Vec2"  -> Just vector2
  "Vec3"  -> Just vector3
  "Vec4"  -> Just vector4
  "int"   -> Just int32
  "float" -> Just float32
  "bool"  -> Just bool
  "vec2"  -> Just vector2
  "vec3"  -> Just vector3
  "vec4"  -> Just vector4
  _       -> Nothing


defaultConfig :: Config
defaultConfig =
  Dict
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

data IdType
  = IdTypeDataType DataType -- done
  | IdTypeConstant Literal -- done
  | IdTypeVariable (Env, String) -- done
  | IdTypeFunction String DataType -- name return type, arguments --tbd
  deriving (Show)

idTypeToKey :: IdType -> String
idTypeToKey d = case d of
  IdTypeDataType t      -> "type " ++ show t
  IdTypeConstant v      -> "const " ++ show v
  IdTypeVariable (e, s) -> "var " ++ show e ++ " " ++ s
  IdTypeFunction s t    -> "func " ++ s ++ " " ++ show t

findId :: IdType -> State -> Maybe OpId
findId id s = Map.lookup (idTypeToKey id) (idMap s)

insertId :: IdType -> State -> (State, OpId)
insertId key state =
  case findId key state of
    Just existingId -> (state, existingId)
    Nothing ->
      let (newMap, newId, newCount) = generateEntry key state
          updatedState = state {idMap = newMap, idCount = newCount}
       in (updatedState, newId)

-- Helper function to generate a new entry for the IdType
generateEntry :: IdType -> State -> (OpIdMap, OpId, Int)
generateEntry key state =
  let currentMap = idMap state
      currentCount = idCount state
   in case key of
        IdTypeDataType t ->
          let idName = IdName (show t)
           in (Map.insert (idTypeToKey key) idName currentMap, idName, currentCount)
        IdTypeConstant l ->
          let idName = case l of
                LBool b  -> IdName ("bool" ++ show b)
                LUint i  -> IdName ("uint" ++ show i)
                LInt i   -> IdName ("int" ++ show i)
                LFloat f -> IdName ("float" ++ show f)
           in (Map.insert (idTypeToKey key) idName currentMap, Id currentCount, currentCount)
        IdTypeVariable (e, s) ->
          let idName = IdName (show e ++ "_" ++ s)
           in (Map.insert (idTypeToKey key) idName currentMap, Id currentCount, currentCount)
        IdTypeFunction s t ->
          let DTypeFunction returnType args = t
              idName = IdName (s ++ "_" ++ intercalate "_" (map show args))
           in (Map.insert (idTypeToKey key) idName currentMap, idName, currentCount)

searchTypeId :: State -> DataType -> OpId
searchTypeId m dt = case findId (IdTypeDataType dt) m of
  Just x  -> x
  Nothing -> error (show dt ++ " type not found")

generateType :: State -> DataType -> (State, OpId, [Instruction])
generateType state dtype =
  case findId (IdTypeDataType dtype) state of
    Just _ -> (state, searchTypeId state dtype, [])
    Nothing ->
      let (state', instruction) = case dtype of
            DTypeVoid -> (state, [])
            DTypeBool -> (state, [])
            DTypeInt _ _ -> (state, [])
            DTypeFloat _ -> (state, [])
            DTypeVector _ baseType -> let (s', id, instrs) = generateType state baseType in (s', instrs)
            DTypeMatrix _ baseType -> let (s', id, instrs) = generateType state baseType in (s', instrs)
            DTypeArray _ baseType -> let (s', id, instrs) = generateType state baseType in (s', instrs)
            DTypePointer _ baseType -> let (s', id, instrs) = generateType state baseType in (s', instrs)
            DTypeStruct _ fields -> foldl (\(s, instrs) field -> let (s', id, instrs') = generateType s field in (s', instrs ++ instrs')) (state, []) fields
            DTypeFunction returnType argsType -> foldl (\(s, instrs) t -> let (s', id, instrs') = generateType s t in (s', instrs ++ instrs')) (state, []) (returnType : argsType)
          (state'', typeId) = insertId (IdTypeDataType dtype) state'
          searchTypeId' = searchTypeId state''

          typeInstruction =
            [ Instruction
                ( Just typeId,
                  case dtype of
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
                      OpTypeFunction (searchTypeId' returnType) (ShowList (map searchTypeId' argTypes))
                )
            ]
          updatedState =
            state''
              { idCount = idCount state'' + 1,
                idMap = idMap state''
              }
       in (updatedState, typeId, instruction ++ typeInstruction)

generateConst :: State -> Literal -> (State, OpId, [Instruction])
generateConst state v =
  let dtype = case v of
        LBool _  -> DTypeBool
        LUint _  -> DTypeInt 32 0
        LInt _   -> DTypeInt 32 1
        LFloat _ -> DTypeFloat 32
      (state', typeId, typeInstruction) = generateType state dtype
      (state'', constId) = insertId (IdTypeConstant v) state'

      constInstruction = [Instruction (Just constId, OpConstant typeId v)]
   in (state'', constId, typeInstruction ++ constInstruction)

generateUniform :: (State, Instructions) -> [Uniform] -> (State, Instructions)
generateUniform (state, inst) =
  foldl
    ( \(accState, accInst) (name, dtype, storage, _) ->
        let (state', typeId, typeInstructions) = generateType accState (DTypePointer storage dtype)

            variableInstruction = [Instruction (Just (IdName name), OpVariable typeId storage)]
            nameInstruction = [Instruction (Nothing, OpName (IdName name) name)]
            uniformsInstruction = [Instruction (Nothing, OpDecorate (IdName name) (Location 0))]

            updatedInst =
              accInst
                { nameFields = nameFields accInst ++ nameInstruction,
                  uniformsFields = uniformsFields accInst ++ uniformsInstruction,
                  constFields = constFields accInst ++ variableInstruction
                }
         in (state', updatedInst)
    )
    (state, inst)

generateInit :: Config -> (State, Instructions)
generateInit h =
  (state, inst)
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

    idMap = Map.insert ("extension " ++ extension h) (Id (startId + 1)) Map.empty
    idCount = startId + 1
    constInstruction = []
    state =
      State
        { idCount = idCount,
          idMap = idMap,
          env = ("", DTypeVoid),
          decs = []
        }
    inst =
      Instructions
        { headerFields = [Instruction (Nothing, Comment "header fields")] ++ headInstruction,
          nameFields = [Instruction (Nothing, Comment "Name fields")],
          uniformsFields = [Instruction (Nothing, Comment "uniform fields")],
          constFields = [Instruction (Nothing, Comment "Const fields")],
          functionFields = [[Instruction (Nothing, Comment "functions fields")]]
        }

generateNegOp :: State -> Variable -> (State, Variable, [Instruction], [Instruction])
generateNegOp state v =
  let id = Id ((idCount state) + 1)
      (e, t, typeId) = (fst v, snd v, searchTypeId state (snd v))
      state' =
        state
          { idCount = idCount state + 1
          }
      instruction =
        case t of
          bool ->
            Instruction (Just id, OpLogicalNot typeId e)
          int32 ->
            Instruction (Just id, OpSNegate typeId e)
          float32 ->
            Instruction (Just id, OpFNegate typeId e)
      inst = [instruction]
      result = (id, t)
   in (state', result, [], inst)

generateBinOp :: State -> Variable -> Ast.Op (Range, Ast.Type Range) -> Variable -> (State, Variable, [Instruction], [Instruction])
generateBinOp state v1 op v2 =
  let id = Id (idCount state + 1)
      (e1, t1, typeId1) = (fst v1, snd v1, searchTypeId state (snd v1))
      (e2, t2, typeId2) = (fst v2, snd v2, searchTypeId state (snd v2))
      state' =
        state
          { idCount = idCount state + 1
          }
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
              Ast.Plus _  -> (t1, Instruction (Just id, OpFAdd typeId1 e1 e2))
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
   in (state', result, [], inst)

typeConvert :: Ast.Type Range -> DataType
typeConvert t = case t of
  Ast.TVar _ (Ast.Name _ n) -> case typeStringConvert n of
    Just x  -> x
    Nothing -> error ("Not implemented" ++ show t)
  Ast.TPar _ t -> typeConvert t
  Ast.TArrow _ t1 t2 ->
    let processArrow :: Ast.Type Range -> ([DataType], DataType)
        processArrow (Ast.TArrow _ t1' t2') =
          let (args, ret) = processArrow t2'
           in (typeConvert t1' : args, ret)
        processArrow t = ([], typeConvert t)

        (argTypes, returnType) = processArrow t
     in DTypeFunction returnType argTypes
  Ast.TApp _ t -> error ("Not implemented App" ++ show t)
  Ast.TUnit _ -> DTypeVoid
  _ -> error ("Not implemented?" ++ show t)

generateExpr :: State -> Ast.Expr (Range, Ast.Type Range) -> (State, ExprReturn, [Instruction], [Instruction])
generateExpr state expr =
  let id = Id (idCount state + 1)
      returnVar = ExprResult (id, float32)
      state' = state {idCount = idCount state + 1}
   in case expr of
        Ast.EInt _ i -> handleConst state' (LInt i) int32
        Ast.EFloat _ f -> handleConst state' (LFloat f) float32
        Ast.EList _ l -> handleList state' l returnVar
        Ast.EPar _ e -> generateExpr state' e
        Ast.EVar (_, t1) (Ast.Name (_, t2) n) -> handleVar state' t1 n
        Ast.EString _ _ -> error "String"
        Ast.EUnit _ -> error "Unit"
        Ast.EApp _ e1 e2 -> handleApp state' e1 e2 returnVar
        Ast.EIfThenElse _ e1 e2 e3 -> handleIfThenElse state' e1 e2 e3
        Ast.ENeg _ e -> handleNeg state' e
        Ast.EBinOp _ e1 op e2 -> handleBinOp state' e1 op e2
        Ast.EOp _ _ -> error "Op"
        Ast.ELetIn _ _ _ -> error "LetIn"
        _ -> error (show expr)

handleConst :: State -> Literal -> DataType -> (State, ExprReturn, [Instruction], [Instruction])
handleConst state lit dtype =
  let (s, id, inst) = generateConst state lit
   in (s, ExprResult (id, dtype), inst, [])

handleList :: State -> [Ast.Expr (Range, Ast.Type Range)] -> ExprReturn -> (State, ExprReturn, [Instruction], [Instruction])
handleList state l returnVar =
  let len = length l
   in error "Not implemented array"

handleVar :: State -> Ast.Type Range -> BS.ByteString -> (State, ExprReturn, [Instruction], [Instruction])
handleVar state t1 n =
  let dType = typeConvert t1
      (state'', var, typeInst, []) = case dType of
        DTypeFunction returnType argsType ->
          -- function
          let (state', typeId, typeInst) = generateType state dType
           in case (typeStringConvert n) of
                Just x ->
                  let (state'', id) = insertId (IdTypeFunction (BS.unpack n) dType) state'
                   in (state'', ExprApplication (Left returnType) dType [], typeInst, [])
                Nothing ->
                  let (state', id) = insertId (IdTypeFunction (BS.unpack n) dType) state'
                   in (state', ExprApplication (Right id) dType [], typeInst, [])
        _ ->
          -- local variable
          let (state', typeId, typeInst) = generateType state dType
              (state'', id) = insertId (IdTypeVariable (env state, BS.unpack n)) state'
           in (state'', ExprResult (id, dType), typeInst, [])
   in (state'', var, typeInst, [])

findVar :: State -> BS.ByteString -> DataType -> Variable
findVar state n dType =
  case findId (IdTypeVariable (env state, BS.unpack n)) state of
    Just x  -> (x, dType)
    Nothing -> error (show n ++ " variable not found")

handleApp :: State -> Ast.Expr (Range, Ast.Type Range) -> Ast.Expr (Range, Ast.Type Range) -> ExprReturn -> (State, ExprReturn, [Instruction], [Instruction])
handleApp state e1 e2 returnVar =
  let (state', var1, typeInst1, inst1) = generateExpr state e1
      (state'', var2, typeInst2, inst2) = generateExpr state' e2
      (state''', var3, typeInst3, inst3) = case var1 of
        ExprApplication funcId (DTypeFunction returnType argTypes) args ->
          let args' = case var2 of
                ExprResult v -> args ++ [v] -- add argument
                _            -> error "Expected ExprResult"
           in case (length args', length argTypes) of
                (l, r) | l == r -> case funcId of
                  Left t   -> error "Not implemented"
                  Right id -> applyFunction state id returnType args'
                (l, r) | l < r ->
                      let (state', typeId, typeInst) = generateType state returnType
                          (state'', id) = insertId (IdTypeVariable (env state, BS.unpack "")) state'
                       in (state'', ExprApplication funcId (DTypeFunction returnType argTypes) args', typeInst1 ++ typeInst2 ++ typeInst3, inst1 ++ inst2 ++ inst3)
                (l, r) | l > r -> error "Too many arguments"
        ExprApplication a _ d -> error (show var1)
        _ -> error (show var1)
   in (state''', var3, typeInst1 ++ typeInst2 ++ typeInst3, inst1 ++ inst2 ++ inst3)

handleConstructor :: State -> DataType -> DataType-> [Variable] -> (State, ExprReturn, [Instruction], [Instruction])
handleConstructor state returnType functionType args =
  let (state', typeId, typeInst) = generateType state returnType
      (state'', id) = insertId (IdTypeVariable (env state, BS.unpack "")) state'
    in (state'', ExprResult(id, returnType), typeInst, [])

applyFunction :: State -> OpId -> DataType -> [Variable] -> (State, ExprReturn, [Instruction], [Instruction])
applyFunction state id returnType args =
  let
      (state', typeId, typeInst) = generateType state returnType

   in -- state'' = insertId (IdTypeVariable (env state) (BS.unpack "")) state'
      -- var = case findId (IdTypeVariable (env state) (BS.unpack "")) state'' of
      --   Just x -> (x, returnType)
      --   Nothing -> error "Variable not found"
      error "Not implemented apply function"

handleIfThenElse :: State -> Ast.Expr (Range, Ast.Type Range) -> Ast.Expr (Range, Ast.Type Range) -> Ast.Expr (Range, Ast.Type Range) -> (State, ExprReturn, [Instruction], [Instruction])
handleIfThenElse state e1 e2 e3 =
  let (state1, ExprResult var1, typeInst1, inst1) = generateExpr state e1
      (state2, var2, typeInst2, inst2) = generateExpr state1 e2
      (state3, var3, typeInst3, inst3) = generateExpr state2 e3
      conditionId = case var1 of
        (id, DTypeBool) -> id
        _               -> error "Expected bool"
      -- todo handle function type
      id = idCount state3
      inst1' = inst1 ++ [Instruction (Nothing, OpBranchConditional conditionId (Id (id + 1)) (Id (id + 2)))]
      inst2' = [Instruction (Just (Id (id + 1)), OpLabel)] ++ inst2 ++ [Instruction (Nothing, OpBranch (Id (id + 3)))]
      inst3' =
        [Instruction (Just (Id (id + 2)), OpLabel)]
          ++ inst3
          ++ [Instruction (Nothing, OpBranch (Id (id + 3)))]
          ++ [Instruction (Just (Id (id + 3)), OpLabel)]
      state4 = state3 {idCount = id + 3}
   in -- todo handle return opid
      (state3, var3, typeInst1 ++ typeInst2 ++ typeInst3, inst1' ++ inst2' ++ inst3')

-- error "Not implemented if then else"

handleNeg :: State -> Ast.Expr (Range, Ast.Type Range) -> (State, ExprReturn, [Instruction], [Instruction])
handleNeg state e =
  let (state', ExprResult var, typeInst1, inst1) = generateExpr state e
      (state'', var', typeInst2, inst2) = generateNegOp state' var
   in (state'', ExprResult var', typeInst1 ++ typeInst2, inst1 ++ inst2)

handleBinOp :: State -> Ast.Expr (Range, Ast.Type Range) -> Ast.Op (Range, Ast.Type Range) -> Ast.Expr (Range, Ast.Type Range) -> (State, ExprReturn, [Instruction], [Instruction])
handleBinOp state e1 op e2 =
  let (state', ExprResult var1, typeInst1, inst1) = generateExpr state e1
      (state'', ExprResult var2, typeInst2, inst2) = generateExpr state' e2
      (state''', var3, typeInst3, inst3) = generateBinOp state'' var1 op var2
   in (state''', ExprResult var3, typeInst1 ++ typeInst2 ++ typeInst3, inst1 ++ inst2 ++ inst3)

notImplemented :: String -> a
notImplemented feature = error (feature ++ " not implemented")

generateFunction :: (State, Instructions) -> DecType -> (State, OpId, Instructions)
generateFunction (state, inst) (Ast.DecAnno _ name t) = (state, IdName "", inst)
generateFunction (state, inst) (Ast.Dec (_, t) (Ast.Name (_, _) name) args e) =
  let (functionType, returnType) =
        if name == "main"
          then
            (DTypeFunction DTypeVoid [], DTypeVoid)
          else
            let DTypeFunction returnType argsType = typeConvert t
                argsType' = map (DTypePointer Function) argsType
             in (DTypeFunction returnType argsType', returnType)
      (state', typeId, typeInstructions) = generateType state functionType
      (state'', funcId) = insertId (IdTypeFunction (BS.unpack name) functionType) state'
      returnTypeId = searchTypeId state'' returnType
      functionParamInst = []
      -- [Instruction (Just funcId, OpFunctionParameter (searchTypeId state'' t) (IdName "args"))]

      funcInst =
        [Instruction (Just funcId, OpFunction returnTypeId None typeId)]
          ++ [Instruction (Nothing, OpFunctionEnd)]
      inst' =
        inst
          { constFields = constFields inst ++ typeInstructions,
            functionFields = functionFields inst ++ [funcInst]
          }
   in -- (state'''', ExprResult var, typeInst, inst') = generateExpr state''' e
      (state', funcId, inst')

generateMainFunction :: (State, Instructions) -> [Uniform] -> DecType -> (State, Instructions)
generateMainFunction (state, inst) uniforms (Ast.Dec (_, t) (Ast.Name (_, _) name) args e) =
  let (functionType, returnType) = (DTypeFunction DTypeVoid [], DTypeVoid)
      (state', typeId, typeInstructions) = generateType state functionType
      (state'', funcId) = insertId (IdTypeFunction (BS.unpack name) functionType) state'
      (state''', inst') = generateUniform (state'', inst) uniforms
      returnTypeId = searchTypeId state'' returnType
      (state'''', ExprResult var, typeInst, exprInst) = generateExpr state''' e

      funcInst =
        [Instruction (Just funcId, OpFunction returnTypeId None typeId)]
          ++ exprInst
          ++ [ Instruction (Nothing, OpReturn),
               Instruction (Nothing, OpFunctionEnd)
             ]
      inst'' =
        inst'
          { constFields = constFields inst ++ typeInstructions ++ typeInst,
            functionFields = functionFields inst' ++ [funcInst]
          }
   in (state''', inst'')

-- error (show exprInst ++ show typeInst)

findDec :: [DecType] -> String -> DecType
findDec decs name =
  case filter (\d -> case d of Ast.Dec (_, _) (Ast.Name (_, _) n) _ _ -> n == BS.pack name; _ -> False) decs of
    [d] -> d
    _   -> error "Main function not found"

instructionsToString :: Instructions -> String
instructionsToString inst =
  let code = headerFields inst ++ nameFields inst ++ uniformsFields inst ++ constFields inst ++ concat (functionFields inst)
      codeText = intercalate "\n" (map show code)
   in codeText

generate :: Config -> [DecType] -> Instructions
generate config decs =
  let init = generateInit config
      (initState, inst) = init
      mainDec = findDec decs (entryPoint config)
      (state', inst') = generateMainFunction (initState, inst) (uniforms config) mainDec

      -- functions = foldl genFunctionCode header decs
      -- -- test = generateConst functions (LInt 1)
      -- -- test =generateType functions (DTypeVoid)
      -- test = functions
      -- test = init
      finalInst = inst'
   in finalInst

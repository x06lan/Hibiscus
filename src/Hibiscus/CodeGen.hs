{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-missing-signatures #-}

module Hibiscus.CodeGen where

-- import qualified Data.Set as Set

import qualified Data.ByteString.Lazy.Char8 as BS
import Data.Fixed (Uni)
import Data.List (intercalate)
import qualified Data.Map as Map
import Hibiscus.Asm
import qualified Hibiscus.Ast as Ast
import Hibiscus.Lexer
import Hibiscus.Parser
import Hibiscus.Type
import Hibiscus.Typing

-- import Data.IntMap (fromList, foldlWithKey)

type Variable = (OpId, DataType)

type Uniform = (String, DataType, StorageClass, Int)

data Config = Dict
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

type OpIdMap = Map.Map String OpId

data Instructions = Instructions
  { headerFields :: [Instruction],
    nameFields :: [Instruction],
    uniformsFields :: [Instruction],
    constFields :: [Instruction],
    functionFields :: [[Instruction]] -- [function]
  }
  deriving (Show)

data State = State
  { idCount :: Int,
    idMap :: OpIdMap
  }
  deriving (Show)

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
  | IdTypeVariable String -- tbd
  | IdTypeFunction String DataType -- name return type, arguments --tbd
  deriving (Show)

idTypeToKey :: IdType -> String
idTypeToKey d = case d of
  IdTypeDataType t -> "type " ++ show t
  IdTypeConstant v -> "const " ++ show v
  IdTypeVariable s -> "var " ++ s
  IdTypeFunction s t -> "func " ++ s ++ " " ++ show t

findId :: IdType -> OpIdMap -> Maybe OpId
findId d = Map.lookup (idTypeToKey d)

insertId :: IdType -> State -> State
insertId key state =
  let m = idMap state
      count = idCount state
   in case findId key m of
        Just _ -> state
        Nothing ->
          state
            { idMap =
                Map.insert
                  (idTypeToKey key)
                  ( case key of
                      IdTypeDataType t -> IdName (show t)
                      IdTypeConstant l ->
                        let name = case l of
                              LUint i -> "uint_" ++ show i
                              LInt i -> "int_" ++ show i
                              LFloat f -> "float_" ++ show f
                         in IdName name
                      IdTypeVariable s -> IdName s
                      IdTypeFunction s t ->
                        IdName
                          ( s
                              ++ ( case t of
                                     DTypeFunction returnType [] -> ""
                                     DTypeFunction returnType argTypes -> "_" ++ (show argTypes)
                                     _ -> error "Invalid function type"
                                 )
                          )
                  )
                  m
            }

searchTypeId :: State -> DataType -> OpId
searchTypeId m dt = case findId (IdTypeDataType dt) (idMap m) of
  Just x -> x
  Nothing -> error (show dt ++ " type not found")

generateType :: State -> DataType -> (State, [Instruction])
generateType state dtype =
  case findId (IdTypeDataType dtype) (idMap state) of
    Just _ -> (state, [])
    Nothing ->
      let (state', instruction) = case dtype of
            DTypeVoid -> (state, [])
            DTypeBool -> (state, [])
            DTypeInt _ _ -> (state, [])
            DTypeFloat _ -> (state, [])
            DTypeVector _ baseType -> generateType state baseType
            DTypeMatrix _ baseType -> generateType state baseType
            DTypeArray _ baseType -> generateType state baseType
            DTypePointer baseType _ -> generateType state baseType
            DTypeStruct _ fields -> foldl (\(s, instrs) field -> let (s', instrs') = generateType s field in (s', instrs ++ instrs')) (state, []) fields
            DTypeFunction returnType argsType -> foldl (\(s, instrs) t -> let (s', instrs') = generateType s t in (s', instrs ++ instrs')) (state, []) (returnType : argsType)
          state'' = insertId (IdTypeDataType dtype) state'
          searchTypeId' = searchTypeId state''
          typeId = searchTypeId' dtype

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
                    DTypePointer baseType storage ->
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
       in (updatedState, instruction ++ typeInstruction)

generateConst :: State -> Literal -> (State, OpId, [Instruction])
generateConst state v =
  let dtype = case v of
        LBool _ -> DTypeBool
        LUint _ -> DTypeInt 32 0
        LInt _ -> DTypeInt 32 1
        LFloat _ -> DTypeFloat 32
      (state', typeInstruction) = generateType state dtype
      state'' = insertId (IdTypeConstant v) state'
      typeId = searchTypeId state'' dtype

      constId = case findId (IdTypeConstant v) (idMap state'') of
        Just x -> x
        Nothing -> error (show v ++ " const not found")
      constInstruction = [Instruction (Just constId, OpConstant typeId v)]
   in (state'', constId, typeInstruction ++ constInstruction)

generateUniform :: (State, Instructions) -> [Uniform] -> (State, Instructions)
generateUniform (state, inst) =
  foldl
    ( \(accState, accInst) (name, dtype, storage, _) ->
        let (state', typeInstructions) = generateType accState (DTypePointer dtype storage)
            pointerTypeId = case findId (IdTypeDataType (DTypePointer dtype storage)) (idMap state') of
              Just x -> x
              Nothing -> error (show dtype ++ show storage ++ "Pointer base not found")

            variableInstruction = [Instruction (Just (IdName name), OpVariable pointerTypeId storage)]
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
          idMap = idMap
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
      (resultType, instruction) =
        case t of
          bool ->
            (bool, Instruction (Just id, OpLogicalNot typeId e))
          int32 ->
            (int32, Instruction (Just id, OpSNegate typeId e))
          float32 ->
            (float32, Instruction (Just id, OpFNegate typeId e))
          _ -> error "Not implemented"
      inst = [instruction]
      result = (id, resultType)
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
              Ast.Plus _ -> (vector2, Instruction (Just id, OpFAdd typeId1 e1 e2))
              Ast.Minus _ -> (vector2, Instruction (Just id, OpFSub typeId1 e1 e2))
              Ast.Times _ -> (vector2, Instruction (Just id, OpFMul typeId1 e1 e2))
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

data ExprReturn
  = ExprResult Variable
  | ExprApplication Variable [Variable]
  deriving (Show)

generateExpr :: State -> Ast.Expr (Range, Ast.Type Range) -> (State, ExprReturn, [Instruction], [Instruction])
generateExpr state expr =
  let id = Id (idCount state + 1)
      returnVar = ExprResult (id, DTypeVoid)
   in case expr of
        Ast.EInt _ i -> let (s, id, inst) = generateConst state (LInt i) in (s, ExprResult (id, int32), inst, [])
        Ast.EFloat _ f -> let (s, id, inst) = generateConst state (LFloat f) in (s, ExprResult (id, float32), inst, [])
        Ast.EList _ l ->
          let len = length l
           in -- (state', returnVar', typeInst, inst) =
              --   foldl
              --     ( \(s, v, t, i) e ->
              --         let (s', v', t', i') = generateExpr s e
              --          in (s', v', t ++ t', i ++ i')
              --     )
              --     (state, returnVar, [], [])
              --     l
              (state, returnVar, [], [])
        -- EApp _ (EOp _ op) e2 ->
        --   let (state', var, typeInst1, inst1) = generateExpr state e2
        --       (state'', var', typeInst2, inst2) = generateSingleOp state' op var
        --       typeInst' = typeInst1 ++ typeInst2
        --       inst' = inst1 ++ inst2
        --    in (state'', var', typeInst', inst')
        -- Ast.EApp _ (Ast.EVar _ (Ast.Name _ n)) e2 -> (state, returnVar, [], [])
        Ast.EApp _ e1 e2 ->
          let (state', var1, typeInst1, inst1) = generateExpr state e1
              (state'', var2, typeInst2, inst2) = generateExpr state' e2
           in (state, returnVar, [], [])
        -- let (state', var1, typeInst1, inst1) = generateExpr state e1
        --     (state'', var2, typeInst2, inst2) = generateExpr state' e2
        -- (state''', var3, typeInst3, inst3) = generateBinOp state'' var1 (Ast.Plus (0, Ast.TUnknown (0, 0))) var2
        -- typeInst' = typeInst1 ++ typeInst2 ++ typeInst3
        -- inst' = inst1 ++ inst2 ++ inst3
        Ast.EPar _ e -> generateExpr state e
        Ast.EVar (_, t1) (Ast.Name (_, t2) n) ->
          let returnVar' = case t1 of
                Ast.TArrow _ t1 t2 ->
                  let varType = DTypeFunction (DTypeVoid) [DTypeInt 32 1] -- todo fix this
                      typeId = searchTypeId state varType
                      var = (IdName (BS.unpack n), varType)
                      returnVar'' = ExprApplication var []
                   in returnVar''
                Ast.TVar _ (Ast.Name _ n) ->
                  let varType = float32
                      typeId = searchTypeId state varType
                      var = (IdName (BS.unpack n), varType)
                      returnVar'' = ExprResult var
                   in returnVar''
           in (state, returnVar, [], [])
        -- error (show n ++ ":" ++ show t1 ++ show t2)
        Ast.EString _ s -> error "String not implemented"
        Ast.EUnit _ -> (state, returnVar, [], []) -- todo fix this
        Ast.EIfThenElse _ e1 e2 e3 ->
          let (state1, ExprResult var1, typeInst1, inst1) = generateExpr state e1
              (state2, var2, typeInst2, inst2) = generateExpr state1 e2
              (state3, var3, typeInst3, inst3) = generateExpr state2 e3
              typeInst' = typeInst1 ++ typeInst2 ++ typeInst3
              inst' = inst1 ++ inst2 ++ inst3
           in (state3, var3, typeInst', inst')
        Ast.ENeg _ e ->
          let (state', ExprResult var, typeInst1, inst1) = generateExpr state e
              (state'', var', typeInst2, inst2) = generateNegOp state' var
              typeInst' = typeInst1 ++ typeInst2
              inst' = inst1 ++ inst2
           in (state'', ExprResult var', typeInst', inst')
        Ast.EBinOp _ e1 op e2 ->
          let (state', ExprResult var1, typeInst1, inst1) = generateExpr state e1
              (state'', ExprResult var2, typeInst2, inst2) = generateExpr state' e2
              (state''', var3, typeInst3, inst3) = generateBinOp state'' var1 op var2
              typeInst' = typeInst1 ++ typeInst2 ++ typeInst3
              inst' = inst1 ++ inst2 ++ inst3
           in (state''', ExprResult var3, typeInst', inst')
        Ast.EOp _ op -> error "Not implemented" -- todo fix this
        Ast.ELetIn _ dec e -> (state, returnVar, [], []) -- todo

genFunction :: (State, Instructions) -> Ast.Dec (Range, Ast.Type Range) -> (State, Instructions)
genFunction (state, inst) (Ast.DecAnno _ name t) = (state, inst)
genFunction (state, inst) (Ast.Dec _ (Ast.Name (_, t) name) args e) =
  let (state', returnVar, typeInst, inst') = generateExpr state e
      inst'' =
        inst
          { constFields = constFields inst ++ typeInst,
            functionFields = functionFields inst ++ [inst']
          }
   in (state', inst'')

instructionsToString :: Instructions -> String
instructionsToString inst =
  let code = headerFields inst ++ nameFields inst ++ uniformsFields inst ++ constFields inst ++ concat (functionFields inst)
      codeText = intercalate "\n" (map show code)
   in codeText

generate :: Config -> [Ast.Dec (Range, Ast.Type Range)] -> Instructions
generate config decs =
  let init = generateInit config
      (initState, inst) = generateUniform init (uniforms config)
      (functions, inst') = foldl genFunction (initState, inst) decs
      -- (state', inst') = foldl genFunction (initState, inst) decs

      -- functions = foldl genFunctionCode header decs
      -- -- test = generateConst functions (LInt 1)
      -- -- test =generateType functions (DTypeVoid)
      -- test = functions
      -- test = init
      finalInst = inst'
   in finalInst

{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-missing-signatures #-}

module Hibiscus.CodeGen.GenExpr where

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
import Hibiscus.CodeGen.Util

import qualified Hibiscus.Type4plus as TI -- type infer

import Control.Monad.State.Lazy
import Data.Monoid (First (..), getFirst)

import Hibiscus.Util (foldMaplM, foldMaprM)

import Hibiscus.CodeGen.Type


----- Below are used by a lot of place

-- TODO: Unfinished Monad-ise
-- Helper function to generate a new entry for the IdType
-- used by insertResultSt
generateEntrySt :: ResultType -> State LanxSt (ExprReturn)
generateEntrySt key = state $ \s ->
  let (newMap, newId, newCount) = generateEntry s key
      s' = s{idMap = newMap, idCount = newCount}
   in (newId, s')

-- Helper function to generate a new entry for the IdType
generateEntry :: LanxSt -> ResultType -> (ResultMap, ExprReturn, Int)
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
          let var = (IdName (intercalate "_" (envs ++ [name])), varType)
              result = ExprResult var
           in (Map.insert key result currentMap, result, currentCount)
        ResultVariableValue ((envName, envType), s, varType) ->
          let var = (Id (currentCount + 1), varType)
              result = ExprResult var
           in (Map.insert key result currentMap, result, currentCount + 1)

-- used by a lot of place
insertResultSt :: ResultType -> Maybe ExprReturn -> State LanxSt (ExprReturn)
insertResultSt key maybeER = do
  state <- get
  case findResult state key of
    Just existingResult -> return existingResult
    Nothing ->
      case maybeER of
        Nothing -> generateEntrySt key
        Just value -> do
          let newMap = Map.insert key value (idMap state)
          put $ state{idMap = newMap}
          return value

generateTypeSt_aux1 :: DataType -> State LanxSt (Instructions)
generateTypeSt_aux1 dType = do
  case dType of
    DTypeUnknown -> error "Unknown type"
    DTypeVoid    -> return emptyInstructions
    DTypeBool    -> return emptyInstructions
    DTypeInt _   -> return emptyInstructions
    DTypeUInt _  -> return emptyInstructions
    DTypeFloat _ -> return emptyInstructions
    DTypeVector _ baseType  -> do (_, inst) <- generateTypeSt baseType; return inst
    DTypeMatrix _ baseType  -> do (_, inst) <- generateTypeSt baseType; return inst
    DTypeArray _ baseType   -> do (_, inst) <- generateTypeSt baseType; return inst
    DTypePointer _ baseType -> do (_, inst) <- generateTypeSt baseType; return inst
    DTypeStruct _ fields              -> foldMaplM (\field -> do (_, inst) <- generateTypeSt field;                     return inst) fields
    DTypeFunction returnType argsType -> foldMaplM (\t ->     do (_, inst) <- generateTypeSt (DTypePointer Function t); return inst) (returnType : argsType)

generateTypeSt_aux2 :: DataType -> ResultId -> State LanxSt (Instructions)
generateTypeSt_aux2 dType typeId = state $ \state2 ->
  let
    searchTypeId' = searchTypeId state2

    -- IDK how this is possible, so I'll leave this magic in the box.
    (state3, inst3) = case dType of
      DTypeUnknown -> error "Unknown type"
      DTypeVoid -> (state2, emptyInstructions{typeFields = [returnedInstruction typeId (OpTypeVoid)]})
      DTypeBool -> (state2, emptyInstructions{typeFields = [returnedInstruction typeId (OpTypeBool)]})
      DTypeInt size -> (state2, emptyInstructions{typeFields = [returnedInstruction typeId (OpTypeInt size 0)]})
      DTypeUInt size -> (state2, emptyInstructions{typeFields = [returnedInstruction typeId (OpTypeInt size 1)]})
      DTypeFloat size -> (state2, emptyInstructions{typeFields = [returnedInstruction typeId (OpTypeFloat size)]})
      DTypeVector size baseType -> (state2, emptyInstructions{typeFields = [returnedInstruction typeId (OpTypeVector (searchTypeId' baseType) size)]})
      DTypeMatrix col baseType -> (state2, emptyInstructions{typeFields = [returnedInstruction typeId (OpTypeMatrix (searchTypeId' baseType) col)]})
      DTypeArray size baseType ->
        let ((constId, inst2), state4) = runState (generateConstSt (LUint size)) state3
            arrayInst = [returnedInstruction typeId (OpTypeArray (searchTypeId' baseType) constId)]
            inst3' = inst2{typeFields = typeFields inst2 ++ arrayInst}
         in (state4, inst3')
      DTypePointer storage DTypeVoid -> (state2, emptyInstructions)
      DTypePointer storage baseType ->
        let pointerInst = [returnedInstruction typeId (OpTypePointer storage (searchTypeId' baseType))]
            inst2' = emptyInstructions{typeFields = pointerInst}
         in (state2, inst2')
      DTypeStruct name baseTypes ->
        let structInst = [returnedInstruction typeId (OpTypeStruct (ShowList (map searchTypeId' baseTypes)))]
            inst2' = emptyInstructions{typeFields = structInst}
         in (state2, inst2')
      DTypeFunction returnType argTypes ->
        let functionInst = [returnedInstruction typeId (OpTypeFunction (searchTypeId' returnType) (ShowList (map (searchTypeId' . DTypePointer Function) argTypes)))]
            inst2' = emptyInstructions{typeFields = functionInst}
         in (state2, inst2')

    updatedState =
      state3
        { idCount = idCount state3
        , idMap = idMap state3
        }
   in
    (inst3, updatedState)

-- used by a lot of place
generateTypeSt :: DataType -> State LanxSt (OpId, Instructions)
generateTypeSt dType = do
  state <- get
  case findResult state (ResultDataType dType) of
    Just (ExprResult (typeId, _)) -> return (typeId, emptyInstructions)
    Nothing -> do
      inst <- generateTypeSt_aux1 dType
      _er  <- insertResultSt (ResultDataType dType) Nothing
      let (ExprResult (typeId, _)) = _er
      inst3 <- generateTypeSt_aux2 dType typeId
      return (typeId, inst +++ inst3)

----- Below are NegOp/BinOp lookup maps (I might wrong)

-- used by generateExprSt (Ast.ENeg _ e)
generateNegOpSt :: Variable -> State LanxSt (Variable, StackInst)
generateNegOpSt v = state $ \state ->
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
                [returnedInstruction id (OpLogicalNot typeId e)]
            | t == int32 ->
                [returnedInstruction id (OpSNegate typeId e)]
            | t == float32 ->
                [returnedInstruction id (OpFNegate typeId e)]
          _ -> error ("not support neg of " ++ show t)
      result = (id, t)
   in ((result, inst), state')

-- TODO: Unfinished Monad-ise
generateBinOpSt :: Variable -> Ast.Op (Range, Type) -> Variable -> State LanxSt (Variable, Instructions, StackInst)
generateBinOpSt v1 op v2 = state $ \s ->
  let (s', v, i, si) = generateBinOp s v1 op v2
   in ((v, i, si), s')

-- used by generateExprSt (Ast.EBinOp _ e1 op e2)
generateBinOp :: LanxSt -> Variable -> Ast.Op (Range, Type) -> Variable -> (LanxSt, Variable, Instructions, StackInst)
generateBinOp state v1@(e1, t1) op v2@(e2, t2) =
  let typeId1 = searchTypeId state t1
      typeId2 = searchTypeId state t2
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
                  Ast.Eq _ -> (bool, returnedInstruction (id) (OpLogicalEqual typeId1 e1 e2))
                  Ast.Neq _ -> (bool, returnedInstruction (id) (OpLogicalNotEqual typeId1 e1 e2))
                  Ast.And _ -> (bool, returnedInstruction (id) (OpLogicalAnd typeId1 e1 e2))
                  Ast.Or _ -> (bool, returnedInstruction (id) (OpLogicalOr typeId1 e1 e2))
            | t1 == int32 && t2 == int32 ->
                case op of
                  Ast.Plus _ -> (int32, returnedInstruction (id) (OpIAdd typeId1 e1 e2))
                  Ast.Minus _ -> (int32, returnedInstruction (id) (OpISub typeId1 e1 e2))
                  Ast.Times _ -> (int32, returnedInstruction (id) (OpIMul typeId1 e1 e2))
                  Ast.Divide _ -> (int32, returnedInstruction (id) (OpSDiv typeId1 e1 e2))
                  Ast.Eq _ -> (bool, returnedInstruction (id) (OpIEqual typeId1 e1 e2))
                  Ast.Neq _ -> (bool, returnedInstruction (id) (OpINotEqual typeId1 e1 e2))
                  Ast.Lt _ -> (bool, returnedInstruction (id) (OpSLessThan typeId1 e1 e2))
                  Ast.Le _ -> (bool, returnedInstruction (id) (OpSLessThanEqual typeId1 e1 e2))
                  Ast.Gt _ -> (bool, returnedInstruction (id) (OpSGreaterThan typeId1 e1 e2))
                  Ast.Ge _ -> (bool, returnedInstruction (id) (OpSGreaterThanEqual typeId1 e1 e2))
            | t1 == int32 && t2 == float32 -> error "Not implemented"
            | t1 == float32 && t2 == int32 -> error "Not implemented"
            | t1 == float32 && t2 == float32 ->
                case op of
                  Ast.Plus _ -> (float32, returnedInstruction (id) (OpFAdd typeId1 e1 e2))
                  Ast.Minus _ -> (float32, returnedInstruction (id) (OpFSub typeId1 e1 e2))
                  Ast.Times _ -> (float32, returnedInstruction (id) (OpFMul typeId1 e1 e2))
                  Ast.Divide _ -> (float32, returnedInstruction (id) (OpFDiv typeId1 e1 e2))
                  Ast.Eq _ -> (bool, returnedInstruction (id) (OpFOrdEqual typeId1 e1 e2))
                  Ast.Neq _ -> (bool, returnedInstruction (id) (OpFOrdNotEqual typeId1 e1 e2))
                  Ast.Lt _ -> (bool, returnedInstruction (id) (OpFOrdLessThan typeId1 e1 e2))
                  Ast.Le _ -> (bool, returnedInstruction (id) (OpFOrdLessThanEqual typeId1 e1 e2))
                  Ast.Gt _ -> (bool, returnedInstruction (id) (OpFOrdGreaterThan typeId1 e1 e2))
                  Ast.Ge _ -> (bool, returnedInstruction (id) (OpFOrdGreaterThanEqual typeId1 e1 e2))
            | t1 == t2 && (t1 == vector2 || t1 == vector3 || t1 == vector4) ->
                case op of
                  Ast.Plus _ -> (t1, returnedInstruction (id) (OpFAdd typeId1 e1 e2))
                  Ast.Minus _ -> (t1, returnedInstruction (id) (OpFSub typeId1 e1 e2))
                  Ast.Times _ -> (t1, returnedInstruction (id) (OpFMul typeId1 e1 e2))
            | (t1 == vector2 || t1 == vector3 || t1 == vector4) && (t2 == int32 || t2 == float32) ->
                case op of
                  Ast.Times _ -> (vector2, returnedInstruction (id) (OpVectorTimesScalar typeId1 e1 e2))
            | (t1 == int32 || t1 == float32) && (t2 == vector2 || t2 == vector3 || t2 == vector4) ->
                case op of
                  Ast.Times _ -> (vector2, returnedInstruction (id) (OpVectorTimesScalar typeId1 e1 e2))
          _ -> error ("Not implemented" ++ show t1 ++ show op ++ show t2)
   in (state', (id, resultType), emptyInstructions, [instruction])

----- Below are directly used by generateExprSt

-- fold aux used by generateExprSt (Ast.ELetIn _ decs e)
generateDecSt :: Dec -> State LanxSt (Instructions, VariableInst, StackInst)
generateDecSt (Ast.DecAnno _ name t) = return mempty
generateDecSt (Ast.Dec (_, t) (Ast.Name (_, _) name) [] e) =
  do
    let varType = typeConvert t
    (typeId, inst1) <- generateTypeSt varType
    (result, inst2, varInst, stackInst) <- generateExprSt e
    -- env_state2 <- gets env
    -- _ <- insertResultSt (ResultVariable (env_state2, BS.unpack name, varType)) (Just result)
    env_state3 <- gets env
    _ <- insertResultSt (ResultVariableValue (env_state3, BS.unpack name, varType)) (Just result)
    return (inst1 +++ inst2, varInst, stackInst)

-- this function is aux of generateFunctionSt
generateFunctionParamSt :: [Ast.Argument (Range, Type)] -> State LanxSt (Instructions, [Instruction])
generateFunctionParamSt args =
  let
    aux :: (String, DataType) -> State LanxSt (Instructions, Instruction)
    aux (name, dType) = do
      (typeId, inst1) <- generateTypeSt (DTypePointer Function dType)
      env_s' <- gets env
      _er <- insertResultSt (ResultVariable (env_s', name, dType)) Nothing
      let (ExprResult (id, _)) = _er
      let paramInst = returnedInstruction (id) (OpFunctionParameter typeId)
      return (inst1, paramInst)
    makeAssociative (is, i) = (is, [i]) -- it's a anti-optimised move, but making less mentally taxing
   in
    do
      foldMaplM (fmap makeAssociative . aux) . fmap getNameAndDType $ args

-- aux used by handleVarFunctionSt
-- used by generateExprSt (Ast.EVar (_, t1) (Ast.Name (_, _) name))
generateFunctionSt :: Instructions -> Dec -> State LanxSt (OpId, Instructions)
generateFunctionSt inst (Ast.DecAnno _ name t) = return (IdName "", inst)
generateFunctionSt inst (Ast.Dec (_, t) (Ast.Name (_, _) name) args e) =
  do
    env_state0 <- gets env
    let functionType = typeConvert t
    let DTypeFunction returnType argsType = functionType

    (typeId, inst1) <- generateTypeSt functionType
    modify (\s -> s{env = ([""], functionType)})
    env_state1 <- gets env

    let funcId = IdName ( intercalate "_" ([BS.unpack name] ++ (map show argsType)))
    let result  = ExprApplication (CustomFunction funcId (BS.unpack name )) (returnType, argsType) []
    er <- insertResultSt (ResultVariableValue (env_state1, BS.unpack name, functionType)) (Just result)

    modify (\s -> s{env = ("":[BS.unpack name], functionType)})

    (inst2, paramInst) <- generateFunctionParamSt args

    modify (\s -> s{idCount = idCount s + 1})
 
    labelId <- gets (Id . idCount)

    (er, inst3, varInst, exprInst) <- generateExprSt e
    let ExprResult (resultId, _) = er

    modify (\s -> s{env = env_state0})

    returnTypeId <- gets (\s -> searchTypeId s returnType)

    let funcInst =
          FunctionInst
            { begin = [commentInstruction $ "function " ++ BS.unpack name, returnedInstruction funcId (OpFunction returnTypeId None typeId)]
            , parameter = paramInst
            , label = [returnedInstruction labelId OpLabel]
            , variable = varInst
            , body = exprInst ++ [noReturnInstruction $ OpReturnValue resultId]
            , end = [noReturnInstruction OpFunctionEnd]
            }
    let inst4 = inst +++ inst1 +++ inst2 +++ inst3
    let inst5 = inst4{functionFields = functionFields inst4 ++ [funcInst]}
    return (funcId, inst5)

-- used by generateExprSt (Ast.EVar (_, t1) (Ast.Name (_, _) name))
handleVarFunctionSt :: String -> FunctionSignature -> State LanxSt VeryImportantTuple
handleVarFunctionSt name (returnType, args) =
  let
    magic x =
      if length args == 1 && returnType == float32
        then x
        else error (name ++ ":" ++ show args)
  in do
    state <- get
    let result = findResult state (ResultVariableValue (env state, name, DTypeFunction returnType args))
    case result of
      Just x -> return (x, emptyInstructions, [],[])
      Nothing ->
        case typeStringConvert name of
          Just x
            | x == returnType -> return (ExprApplication (TypeConstructor returnType) (returnType, args) [], emptyInstructions, [],[])
          Nothing
            | name == "foldl" -> return (ExprApplication FunctionFoldl (returnType, args) [], emptyInstructions, [],[])
            | name == "map" -> return (ExprApplication FunctionMap (returnType, args) [], emptyInstructions, [],[])
            | name == "extract_0" -> magic $ return (ExprApplication (TypeExtractor returnType [0]) (returnType, args) [], mempty, [],[])
            | name == "extract_1" -> magic $ return (ExprApplication (TypeExtractor returnType [1]) (returnType, args) [], mempty, [],[])
            | name == "extract_2" -> magic $ return (ExprApplication (TypeExtractor returnType [2]) (returnType, args) [], mempty, [],[])
            | name == "extract_3" -> magic $ return (ExprApplication (TypeExtractor returnType [3]) (returnType, args) [], mempty, [],[])
            | True ->
              do
                let dec = fromMaybe (error (name ++ show args)) (findDec (decs state) name Nothing)
                (id, inst1) <- generateFunctionSt emptyInstructions dec

                -- if name =="sub" then
                --   return $ (error . show) (idMap state)
                -- else
                --   return (ExprApplication (CustomFunction id name) (returnType, args) [], inst1, [],[])
                -- return $ (error . show) (idMap state)
                return (ExprApplication (CustomFunction id name) (returnType, args) [], inst1, [],[])
          -- error (show id ++ show (functionFields inst1))
          -- case findResult state (ResultFunction name ) of {}
          _ -> error "Not implemented function"

-- used by handleConstSt
-- used by generateExprSt literals
generateConstSt :: Literal -> State LanxSt (OpId, Instructions)
generateConstSt v = do
  let dtype = dtypeof v
  (typeId, typeInst) <- generateTypeSt dtype
  er <- insertResultSt (ResultConstant v) Nothing
  let (ExprResult (constId, dType)) = er
  let constInstruction = [returnedInstruction constId (OpConstant typeId v)]
  let inst = typeInst{constFields = constFields typeInst ++ constInstruction}
  return (constId, inst)

-- used by generateExprSt literals
handleConstSt :: Literal -> State LanxSt VeryImportantTuple
handleConstSt lit =
  do
    (id, inst) <- generateConstSt lit
    return (ExprResult (id, dtypeof lit), inst, [], [])

----- Below are use by generateExprSt (Ast.EApp _ e1 e2)

applyFunctionSt_aux1 :: (OpId, (OpId, b)) -> State LanxSt ([(OpId, (OpId, b))], [Instruction], [Instruction])
applyFunctionSt_aux1 (typeId, t) =
  do
    id <- gets idCount
    let varId = IdName ("param_" ++ show id)
    modify (\s -> s{idCount = idCount s + 1})
    return
      ( [(varId, t)]
      , [returnedInstruction varId (OpVariable typeId Function)]
      , [noReturnInstruction (OpStore varId (fst t))]
      )

applyFunctionSt :: OpId -> DataType -> [Variable] -> State LanxSt VeryImportantTuple
applyFunctionSt id returnType args =
  do
    searchTypeId_state0_returnType <- gets (\s -> searchTypeId s returnType) -- FIXME: please rename this
    let makeAssociative (id, inst) = ([id], inst)
    (typeIds, inst1) <- foldMaprM (fmap makeAssociative . generateTypeSt . DTypePointer Function . snd) args

    modify (\s -> s{idCount = idCount s + 1})
    (vars, varInst, stackInst) <- foldMaplM applyFunctionSt_aux1 $ zip typeIds args

    resultId <- gets (Id . idCount)
    let stackInst' = returnedInstruction (resultId) (OpFunctionCall (searchTypeId_state0_returnType) id (ShowList (map fst vars)))
    -- (state', vars, typeInst, inst') = foldl (\(s, v, t, i) arg -> let (s', v', t', i') = functionPointer s arg in (s', v' : v, t ++ t', i ++ i')) (state, [], [], []) args
    -- state' = state {idCount = idCount state + 1}
    return (ExprResult (resultId, returnType), inst1, varInst, stackInst ++ [stackInst'])

handleConstructorSt :: DataType -> DataType -> [Variable] -> State LanxSt VeryImportantTuple
handleConstructorSt returnType functionType args =
  do
    (typeId, inst) <- generateTypeSt returnType
    modify (\s -> s{idCount = idCount s + 1})
    returnId <- gets (Id . idCount) -- handle type convert
    let stackInst = [returnedInstruction (returnId) (OpCompositeConstruct typeId (ShowList (map fst args)))]
    return (ExprResult (returnId, returnType), inst, [], stackInst)

handleExtractSt :: DataType -> [Int] -> Variable -> State LanxSt VeryImportantTuple
handleExtractSt returnType i var@(opId, _) =
  do
    (typeId, inst) <- generateTypeSt returnType
    modify (\s -> s{idCount = idCount s + 1})
    returnId <- gets (Id . idCount)
    let stackInst = [returnedInstruction (returnId) (OpCompositeExtract typeId opId (ShowList i))]
    return (ExprResult (returnId, returnType), inst, [], stackInst)

----- Below are stateless

handleOp' :: Expr -> ExprReturn
handleOp' (Ast.EOp _ op) =
  let funcSign = case op of
        Ast.Plus _   -> (DTypeUnknown, [DTypeUnknown, DTypeUnknown])
        Ast.Minus _  -> (DTypeUnknown, [DTypeUnknown])
        Ast.Times _  -> (DTypeUnknown, [DTypeUnknown, DTypeUnknown])
        Ast.Divide _ -> (DTypeUnknown, [DTypeUnknown, DTypeUnknown])
        Ast.Eq _     -> (bool,         [DTypeUnknown, DTypeUnknown])
        Ast.Neq _    -> (bool,         [DTypeUnknown, DTypeUnknown])
        Ast.Lt _     -> (bool,         [DTypeUnknown, DTypeUnknown])
        Ast.Le _     -> (bool,         [DTypeUnknown, DTypeUnknown])
        Ast.Gt _     -> (bool,         [DTypeUnknown, DTypeUnknown])
        Ast.Ge _     -> (bool,         [DTypeUnknown, DTypeUnknown])
        Ast.And _    -> (DTypeUnknown, [DTypeUnknown, DTypeUnknown])
        Ast.Or _     -> (DTypeUnknown, [DTypeUnknown, DTypeUnknown])
   in ExprApplication (OperatorFunction op) funcSign []

-----

generateExprSt :: Expr -> State LanxSt VeryImportantTuple
generateExprSt (Ast.EPar _ e) = generateExprSt e
generateExprSt (Ast.EBool _ x)  = handleConstSt (LBool x)
generateExprSt (Ast.EInt _ x)   = handleConstSt (LInt x)
generateExprSt (Ast.EFloat _ x) = handleConstSt (LFloat x)
generateExprSt (Ast.EList _ es) =
  do
    let len = length es
    let makeAssociative (a, b, c, d) = ([a], b, c, d)
    (results, inst, var, stackInst) <- foldMaplM (fmap makeAssociative . generateExprSt) es
    (typeId, typeInst) <- generateTypeSt (DTypeArray len DTypeUnknown)
    error "Not implemented array"
generateExprSt (Ast.EVar (_, t1) (Ast.Name (_, _) name)) =
  do
    state <- get
    let dType = typeConvert t1
    let maybeResult = findResult state (ResultVariableValue (env state, BS.unpack name, dType))
    case maybeResult of
      Just x -> return (x, mempty, [], [])
      Nothing ->
        case dType of
          DTypeFunction returnType args -> handleVarFunctionSt (BS.unpack name) (returnType, args)
          _ -> 
            do
              let ExprResult (varId, varType) = fromMaybe (error ("can find var:" ++ show (env state, BS.unpack name, dType))) (findResult state (ResultVariable (env state, BS.unpack name, dType)))
              er <- insertResultSt (ResultVariableValue (env state, BS.unpack name, dType)) Nothing
              let  ExprResult (valueId, _) =er 
              state2 <- get
              let inst = returnedInstruction (valueId) (OpLoad (searchTypeId state2 varType) varId)
              return ( ExprResult (valueId, varType), mempty , [], [inst])

generateExprSt (Ast.EString _ _) = error "String"
generateExprSt (Ast.EUnit _) = error "Unit"
generateExprSt (Ast.EApp _ e1 e2) =
  do
    (var1, inst1, varInst1, stackInst1) <- generateExprSt e1
    (var2, inst2, varInst2, stackInst2) <- generateExprSt e2
    (var3, inst3, varInst3, stackInst3) <-
      case var1 of
        ExprApplication funcType (returnType, argTypes) args ->
          let args' = case var2 of
                ExprResult v -> args ++ [v] -- add argument
                _ -> error "Expected ExprResult"
              functionType = DTypeFunction returnType argTypes
           in case (length args', length argTypes) of
                (l, r) | l == r ->
                  case funcType of
                    CustomFunction id s -> applyFunctionSt id returnType args'
                    TypeConstructor t   -> handleConstructorSt t functionType args'
                    TypeExtractor t int -> handleExtractSt t int (head args')
                    OperatorFunction op -> error "Not implemented" -- TODO:
                (l, r) | l < r ->
                  -- uncompleted applicatoin
                  return $ (ExprApplication funcType (returnType, argTypes) args', mempty, [], [])
                (l, r) | l > r -> error "Too many arguments"
        _ -> error (show var1 ++ show var2)
    let finalVar   = var3
    let inst'      = inst1 +++ inst2 +++ inst3
    let varInst'   = varInst1 ++ varInst2 ++ varInst3
    let stackInst' = stackInst1 ++ stackInst2 ++ stackInst3
    return (finalVar, inst', varInst', stackInst')
generateExprSt (Ast.EIfThenElse _ cond thenE elseE) =
  let
    getIdFromBool :: ExprReturn -> OpId
    getIdFromBool (ExprResult (id, DTypeBool)) = id
    getIdFromBool _ = error "Expected bool"
  in do
    (condResult, inst1, varInst1, stackInst1) <- generateExprSt cond
    let conditionId = getIdFromBool condResult
    (var2, inst2, varInst2, stackInst2) <- generateExprSt thenE
    (var3, inst3, varInst3, stackInst3) <- generateExprSt elseE
    id <- gets idCount
    let sInst1' = stackInst1 ++ [noReturnInstruction (OpBranchConditional conditionId (Id (id + 1)) (Id (id + 2)))]
    let sInst2' = [returnedInstruction ((Id (id + 1))) (OpLabel)] ++ stackInst2 ++ [noReturnInstruction (OpBranch (Id (id + 3)))]
    let sInst3' =
          [returnedInstruction ((Id (id + 2))) (OpLabel)]
            ++ stackInst3
            ++ [noReturnInstruction (OpBranch (Id (id + 3)))]
            ++ [returnedInstruction (Id (id + 3)) (OpLabel)]
    -- modify (\s -> s{idCount = id + 3})
    -- TODO: handle return variable
    return (var3, inst1 +++ inst2 +++ inst3, varInst1 ++ varInst2 ++ varInst3, sInst1' ++ sInst2' ++ sInst3')
generateExprSt (Ast.ENeg _ e) =
  do
    (_er, inst1, varInst1, stackInst1) <- generateExprSt e
    let (ExprResult var) = _er
    (var', stackInst2) <- generateNegOpSt var
    return (ExprResult var', inst1, varInst1, stackInst1 ++ stackInst2)
generateExprSt (Ast.EBinOp _ e1 op e2) =
  do
    (_er, inst1, varInst1, stackInst1) <- generateExprSt e1
    let ExprResult var1 = _er
    (_er, inst2, varInst2, stackInst2) <- generateExprSt e2
    let ExprResult var2 = _er
    (var3, inst3, stackInst3) <- generateBinOpSt var1 op var2
    return (ExprResult var3, inst1 +++ inst2 +++ inst3, varInst1 ++ varInst2, stackInst1 ++ stackInst2 ++ stackInst3)
generateExprSt e@(Ast.EOp _ _) = do return (handleOp' e, mempty, [], [])
generateExprSt (Ast.ELetIn _ decs e) =
  do
    (envs, envType) <- gets env
    modify (\s -> s{env = (envs ++ ["letIn"], envType)})
    (inst, varInst, stackInst) <- foldMaprM generateDecSt decs -- reverse order
    (result, inst1, varInst2, stackInst1) <- generateExprSt e
    modify (\s -> s{env = (envs, envType)})
    return (result, inst +++ inst1, varInst ++ varInst2, stackInst ++ stackInst1)
    -- in error (show (findResult state2 (ResultVariableValue (env state2, "x", envType))))
    -- in error (show (idMap state2))
    -- in error (show decs)

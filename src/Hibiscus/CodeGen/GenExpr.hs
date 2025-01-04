{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-missing-signatures #-}

{-# HLINT ignore "Avoid lambda using `infix`" #-}

module Hibiscus.CodeGen.GenExpr where

-- import qualified Data.Set as Set

import Control.Monad.State.Lazy
import qualified Data.ByteString.Lazy.Char8 as BS
import Data.List (find, intercalate, tails)
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid (First (..), getFirst)
import Data.STRef (newSTRef)
import Debug.Trace (traceM)
import qualified Hibiscus.Asm as Asm
import qualified Hibiscus.Ast as Ast
import Hibiscus.CodeGen.Constants (global)
import Hibiscus.CodeGen.Type.Bulitin
import Hibiscus.CodeGen.Types
import Hibiscus.CodeGen.Type.DataType (DataType)
import qualified Hibiscus.CodeGen.Type.DataType as DT
import Hibiscus.CodeGen.Util
import qualified Hibiscus.Parsing.Lexer as L
import qualified Hibiscus.TypeInfer as TI
import Hibiscus.Util (foldMaplM, foldMaprM)


type VeryImportantTuple = (ExprReturn, Instructions, VariableInst, StackInst)

----- Below are used by a lot of place

-- Helper function to generate a new entry for the IdType
-- used by insertResultSt
generateEntrySt :: ResultType -> State LanxSt ExprReturn
generateEntrySt key =
  let
    returnAndUpdateMap :: ExprReturn -> State LanxSt ExprReturn
    returnAndUpdateMap er = do
      modify (\s -> s{idMap = Map.insert key er $ idMap s})
      return er
    flattenTuples :: [(String, DataType)] -> [String]
    flattenTuples = concatMap (\(x, y) -> [x, show y])
   in
    case key of
      ResultDataType t -> do
        returnAndUpdateMap $ ExprResult (Asm.IdName $ show t, t)
      ResultConstant lit -> do
        let opid = Asm.IdName . idNameOf $ lit
        let litType = dtypeof lit
        returnAndUpdateMap $ ExprResult (opid, litType)
      ResultVariable (envs, name, varType) -> do
        let nameWithEnv = intercalate "_" (flattenTuples envs ++ [name])
        let opid = Asm.IdName nameWithEnv
        returnAndUpdateMap $ ExprResult (opid, varType)
      ResultVariableValue (_, _, varType) -> do
        varId <- nextOpId
        returnAndUpdateMap $ ExprResult (varId, varType)

-- TODO: unwrap this function to two function
insertResultSt :: ResultType -> Maybe ExprReturn -> State LanxSt ExprReturn
insertResultSt key maybeER = do
  state <- get
  case findResult state key of
    Just existingResult -> return existingResult
    Nothing ->
      case maybeER of
        Nothing -> generateEntrySt key
        Just value -> do
          modify (\s -> s{idMap = Map.insert key value $ idMap s})
          return value

generateTypeSt_aux1 :: DataType -> State LanxSt Instructions
generateTypeSt_aux1 dType = do
  case dType of
    DT.DTypeUnknown -> error "Unknown type"
    DT.DTypeVoid -> return emptyInstructions
    DT.DTypeBool -> return emptyInstructions
    DT.DTypeInt _ -> return emptyInstructions
    DT.DTypeUInt _ -> return emptyInstructions
    DT.DTypeFloat _ -> return emptyInstructions
    DT.DTypeVector _ baseType -> fmap snd . generateTypeSt $ baseType
    DT.DTypeMatrix _ baseType -> fmap snd . generateTypeSt $ baseType
    DT.DTypeArray _ baseType -> fmap snd . generateTypeSt $ baseType
    DT.DTypePointer _ baseType -> fmap snd . generateTypeSt $ baseType
    DT.DTypeStruct _ fields -> foldMaplM (fmap snd . generateTypeSt) fields
    DT.DTypeFunction returnType argsType -> foldMaplM (fmap snd . generateTypeSt . DT.DTypePointer Asm.Function) (returnType : argsType)

generateTypeSt_aux2 :: DataType -> Asm.ResultId -> State LanxSt Instructions
generateTypeSt_aux2 dType typeId = state $ \state2 ->
  let
    searchTypeId' = searchTypeId state2

    -- IDK how this is possible, so I'll leave this magic in the box.
    (state3, inst3) = case dType of
      DT.DTypeUnknown -> error "Unknown type"
      DT.DTypeVoid -> (state2, emptyInstructions{typeFields = [returnedInstruction typeId Asm.OpTypeVoid]})
      DT.DTypeBool -> (state2, emptyInstructions{typeFields = [returnedInstruction typeId Asm.OpTypeBool]})
      DT.DTypeInt size -> (state2, emptyInstructions{typeFields = [returnedInstruction typeId (Asm.OpTypeInt size 0)]})
      DT.DTypeUInt size -> (state2, emptyInstructions{typeFields = [returnedInstruction typeId (Asm.OpTypeInt size 1)]})
      DT.DTypeFloat size -> (state2, emptyInstructions{typeFields = [returnedInstruction typeId (Asm.OpTypeFloat size)]})
      DT.DTypeVector size baseType -> (state2, emptyInstructions{typeFields = [returnedInstruction typeId (Asm.OpTypeVector (searchTypeId' baseType) size)]})
      DT.DTypeMatrix col baseType -> (state2, emptyInstructions{typeFields = [returnedInstruction typeId (Asm.OpTypeMatrix (searchTypeId' baseType) col)]})
      DT.DTypeArray size baseType ->
        let ((ExprResult (constId, _), inst2, _, _), state4) = runState (generateConstSt (Asm.LUint size)) state3
            arrayInst = [returnedInstruction typeId (Asm.OpTypeArray (searchTypeId' baseType) constId)]
            inst3' = inst2{typeFields = typeFields inst2 ++ arrayInst}
         in (state4, inst3')
      DT.DTypePointer storage DT.DTypeVoid -> (state2, emptyInstructions)
      DT.DTypePointer storage baseType ->
        let pointerInst = [returnedInstruction typeId (Asm.OpTypePointer storage (searchTypeId' baseType))]
            inst2' = emptyInstructions{typeFields = pointerInst}
         in (state2, inst2')
      DT.DTypeStruct name baseTypes ->
        let structInst = [returnedInstruction typeId (Asm.OpTypeStruct (Asm.ShowList (map searchTypeId' baseTypes)))]
            inst2' = emptyInstructions{typeFields = structInst}
         in (state2, inst2')
      DT.DTypeFunction returnType argTypes ->
        let functionInst = [returnedInstruction typeId (Asm.OpTypeFunction (searchTypeId' returnType) (Asm.ShowList (map (searchTypeId' . DT.DTypePointer Asm.Function) argTypes)))]
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
generateTypeSt :: DataType -> State LanxSt (Asm.OpId, Instructions)
generateTypeSt dType = do
  state <- get
  case findResult state (ResultDataType dType) of
    Just (ExprResult (typeId, _)) -> return (typeId, emptyInstructions)
    Nothing -> do
      inst <- generateTypeSt_aux1 dType
      _er <- insertResultSt (ResultDataType dType) Nothing
      let (ExprResult (typeId, _)) = _er
      inst3 <- generateTypeSt_aux2 dType typeId
      return (typeId, inst +++ inst3)

----- Below are NegOp/BinOp lookup maps (I might wrong)

-- used by generateExprSt (Ast.ENeg _ e)
generateNegOpSt :: Variable -> State LanxSt (Variable, StackInst)
generateNegOpSt v@(e, t) =
  do
    id <- nextOpId
    typeId <- gets (\s -> searchTypeId s t)
    let asmop =
          case t of
            t | t == DT.bool -> Asm.OpLogicalNot typeId e
              | t == DT.int32 -> Asm.OpSNegate typeId e
              | t == DT.float32 -> Asm.OpFNegate typeId e
            _ -> error ("not support neg of " ++ show t)
    let inst = returnedInstruction id asmop
    let result = (id, t)
    return (result, [inst])

-- used by generateExprSt (Ast.EBinOp _ e1 op e2)
generateBinOpSt :: Variable -> Ast.Op (L.Range, Type) -> Variable -> State LanxSt (Variable, Instructions, StackInst)
generateBinOpSt v1@(e1, t1) op v2@(e2, t2) =
  do
      typeId1 <- gets (\s -> searchTypeId s t1)
      typeId2 <- gets (\s -> searchTypeId s t2)
      (boolId, inst) <- generateTypeSt DT.DTypeBool
      id <- nextOpId
      let (resultType, instruction) =
            case (t1, t2) of
              (t1, t2)
                | t1 == DT.bool && t2 == DT.bool ->
                    case op of
                      Ast.Eq _ -> (DT.bool, returnedInstruction id (Asm.OpLogicalEqual boolId e1 e2))
                      Ast.Neq _ -> (DT.bool, returnedInstruction id (Asm.OpLogicalNotEqual boolId e1 e2))
                      Ast.And _ -> (DT.bool, returnedInstruction id (Asm.OpLogicalAnd boolId e1 e2))
                      Ast.Or _ -> (DT.bool, returnedInstruction id (Asm.OpLogicalOr boolId e1 e2))
                | t1 == DT.int32 && t2 == DT.int32 ->
                    case op of
                      Ast.Plus _ -> (DT.int32, returnedInstruction id (Asm.OpIAdd typeId1 e1 e2))
                      Ast.Minus _ -> (DT.int32, returnedInstruction id (Asm.OpISub typeId1 e1 e2))
                      Ast.Times _ -> (DT.int32, returnedInstruction id (Asm.OpIMul typeId1 e1 e2))
                      Ast.Divide _ -> (DT.int32, returnedInstruction id (Asm.OpSDiv typeId1 e1 e2))
                      Ast.Eq _ -> (DT.bool, returnedInstruction id (Asm.OpIEqual boolId e1 e2))
                      Ast.Neq _ -> (DT.bool, returnedInstruction id (Asm.OpINotEqual boolId e1 e2))
                      Ast.Lt _ -> (DT.bool, returnedInstruction id (Asm.OpSLessThan boolId e1 e2))
                      Ast.Le _ -> (DT.bool, returnedInstruction id (Asm.OpSLessThanEqual boolId e1 e2))
                      Ast.Gt _ -> (DT.bool, returnedInstruction id (Asm.OpSGreaterThan boolId e1 e2))
                      Ast.Ge _ -> (DT.bool, returnedInstruction id (Asm.OpSGreaterThanEqual boolId e1 e2))
                | t1 == DT.int32 && t2 == DT.float32 -> error "Not implemented"
                | t1 == DT.float32 && t2 == DT.int32 -> error "Not implemented"
                | t1 == DT.float32 && t2 == DT.float32 ->
                    case op of
                      Ast.Plus _ -> (DT.float32, returnedInstruction id (Asm.OpFAdd typeId1 e1 e2))
                      Ast.Minus _ -> (DT.float32, returnedInstruction id (Asm.OpFSub typeId1 e1 e2))
                      Ast.Times _ -> (DT.float32, returnedInstruction id (Asm.OpFMul typeId1 e1 e2))
                      Ast.Divide _ -> (DT.float32, returnedInstruction id (Asm.OpFDiv typeId1 e1 e2))
                      Ast.Eq _ -> (DT.bool, returnedInstruction id (Asm.OpFOrdEqual boolId e1 e2))
                      Ast.Neq _ -> (DT.bool, returnedInstruction id (Asm.OpFOrdNotEqual boolId e1 e2))
                      Ast.Lt _ -> (DT.bool, returnedInstruction id (Asm.OpFOrdLessThan boolId e1 e2))
                      Ast.Le _ -> (DT.bool, returnedInstruction id (Asm.OpFOrdLessThanEqual boolId e1 e2))
                      Ast.Gt _ -> (DT.bool, returnedInstruction id (Asm.OpFOrdGreaterThan boolId e1 e2))
                      Ast.Ge _ -> (DT.bool, returnedInstruction id (Asm.OpFOrdGreaterThanEqual boolId e1 e2))
                | t1 == t2 && (t1 == DT.vector2 || t1 == DT.vector3 || t1 == DT.vector4) ->
                    case op of
                      Ast.Plus _ -> (t1, returnedInstruction id (Asm.OpFAdd typeId1 e1 e2))
                      Ast.Minus _ -> (t1, returnedInstruction id (Asm.OpFSub typeId1 e1 e2))
                      Ast.Times _ -> (t1, returnedInstruction id (Asm.OpFMul typeId1 e1 e2))
                | (t1 == DT.vector2 || t1 == DT.vector3 || t1 == DT.vector4) && (t2 == DT.int32 || t2 == DT.float32) ->
                    case op of
                      Ast.Times _ -> (DT.vector2, returnedInstruction id (Asm.OpVectorTimesScalar typeId1 e1 e2))
                | (t1 == DT.int32 || t1 == DT.float32) && (t2 == DT.vector2 || t2 == DT.vector3 || t2 == DT.vector4) ->
                    case op of
                      Ast.Times _ -> (DT.vector2, returnedInstruction id (Asm.OpVectorTimesScalar typeId1 e1 e2))
              _ -> error ("Not implemented" ++ show t1 ++ show op ++ show t2)
      return ((id, resultType), inst, [instruction])

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
    -- idMap should not have insert key
    _ <- insertResultSt (ResultVariableValue (env_state3, BS.unpack name, varType)) (Just result)
    return (inst1 +++ inst2, varInst, stackInst)

-- this function is aux of generateFunctionSt
generateFunctionParamSt :: [Ast.Argument (L.Range, Type)] -> State LanxSt (Instructions, [Asm.Instruction])
generateFunctionParamSt args =
  let
    aux :: (String, DataType) -> State LanxSt (Instructions, Asm.Instruction)
    aux (name, dType) = do
      (typeId, inst1) <- generateTypeSt (DT.DTypePointer Asm.Function dType)
      env_s' <- gets env
      _er <- insertResultSt (ResultVariable (env_s', name, dType)) Nothing
      let (ExprResult (id, _)) = _er
      let paramInst = returnedInstruction id (Asm.OpFunctionParameter typeId)
      return (inst1, paramInst)
    makeAssociative (is, i) = (is, [i]) -- it's a anti-optimised move, but making less mentally taxing
   in
    do
      foldMaplM (fmap makeAssociative . aux) . fmap getNameAndDType $ args

-- aux used by handleVarFunctionSt
-- used by generateExprSt (Ast.EVar (_, t1) (Ast.Name (_, _) name))
generateFunctionSt :: Instructions -> Dec -> State LanxSt (Asm.OpId, Instructions)
generateFunctionSt inst (Ast.DecAnno _ name t) = return (Asm.IdName "", inst)
generateFunctionSt inst (Ast.Dec (_, t) (Ast.Name (_, _) name) args e) =
  do
    env_state0 <- gets env
    let functionType = typeConvert t
    let DT.DTypeFunction returnType argsType = functionType

    (typeId, inst1) <- generateTypeSt functionType
    modify (\s -> s{env = [global]})
    env_state1 <- gets env

    let funcId = Asm.IdName (intercalate "_" $ BS.unpack name : map show argsType)
    let result = ExprApplication (CustomFunction funcId (BS.unpack name)) (returnType, argsType) []
    er <- insertResultSt (ResultVariableValue (env_state1, BS.unpack name, functionType)) (Just result)

    -- traceM (show (BS.unpack name,env_state1,  functionType, er))

    state <- get

    modify (\s -> s{env = global : [(BS.unpack name, functionType)]})

    (inst2, paramInst) <- generateFunctionParamSt args

    labelId <- nextOpId

    (er, inst3, varInst, exprInst) <- generateExprSt e
    let ExprResult (resultId, _) = er

    modify (\s -> s{env = env_state0})

    returnTypeId <- gets (\s -> searchTypeId s returnType)

    let funcInst =
          FunctionInst
            { begin = [commentInstruction $ "function " ++ BS.unpack name, returnedInstruction funcId (Asm.OpFunction returnTypeId Asm.None typeId)]
            , parameter = paramInst
            , label = [returnedInstruction labelId Asm.OpLabel]
            , variable = varInst
            , body = exprInst ++ [noReturnInstruction $ Asm.OpReturnValue resultId]
            , end = [noReturnInstruction Asm.OpFunctionEnd]
            }
    let inst4 = inst +++ inst1 +++ inst2 +++ inst3
    let inst5 = inst4{functionFields = functionFields inst4 ++ [funcInst]}
    -- state' <- get
    -- return $ error (show $ idMap state')
    return (funcId, inst5)

-- used by generateExprSt (Ast.EVar (_, t1) (Ast.Name (_, _) name))
handleVarFunctionSt :: String -> FunctionSignature -> State LanxSt VeryImportantTuple
handleVarFunctionSt name fs@(returnType, args) =
  case getBulitinFunction name fs of
    Just er -> return (er, mempty, [], [])
    Nothing ->
      do
        state1 <- get
        let dec = fromMaybe (error (name ++ show args)) (findDec (decs state1) name Nothing)
        (id, inst1) <- generateFunctionSt emptyInstructions dec
        -- state2 <- get

        -- doTrace ("after "++ show (env state2)++show (findResult state2 (ResultVariableValue (env state2, name, DTypeFunction returnType args))))
        -- doTrace (show (idMap state2))
        return (ExprApplication (CustomFunction id name) (returnType, args) [], inst1, [], [])

-- used by generateExprSt literals
generateConstSt :: Asm.Literal -> State LanxSt VeryImportantTuple
generateConstSt v =  do
  state <- get
  case findResult state (ResultConstant v) of
    Just x -> return (x, mempty, [], [])
    Nothing ->
        do
          let dtype = dtypeof v
          (typeId, typeInst) <- generateTypeSt dtype
          er <- insertResultSt (ResultConstant v) Nothing
          let (ExprResult (constId, dType)) = er
          let constInstruction = [returnedInstruction constId (Asm.OpConstant typeId v)]
          let inst = typeInst{constFields = constFields typeInst ++ constInstruction}
          return (ExprResult (constId, dtype), inst, [], [])

----- Below are use by generateExprSt (Ast.EApp _ e1 e2)

applyFunctionSt_aux1 :: (Asm.OpId, (Asm.OpId, b)) -> State LanxSt ([(Asm.OpId, (Asm.OpId, b))], VariableInst, StackInst)
applyFunctionSt_aux1 (typeId, t) =
  do
    varId <- nextOpIdName (\i -> "param_" ++ show i)
    return
      ( [(varId, t)]
      , [returnedInstruction varId (Asm.OpVariable typeId Asm.Function)]
      , [noReturnInstruction (Asm.OpStore varId (fst t))]
      )

applyFunctionSt :: Asm.OpId -> DataType -> [Variable] -> State LanxSt VeryImportantTuple
applyFunctionSt id returnType args =
  do
    searchTypeId_state0_returnType <- gets (\s -> searchTypeId s returnType) -- FIXME: please rename this
    let makeAssociative (id, inst) = ([id], inst)
    (typeIds, inst1) <- foldMaprM (fmap makeAssociative . generateTypeSt . DT.DTypePointer Asm.Function . snd) args

    (vars, varInst, stackInst) <- foldMaplM applyFunctionSt_aux1 $ zip typeIds args

    resultId <- nextOpId
    let stackInst' = returnedInstruction resultId (Asm.OpFunctionCall searchTypeId_state0_returnType id (Asm.ShowList (map fst vars)))
    -- (state', vars, typeInst, inst') = foldl (\(s, v, t, i) arg -> let (s', v', t', i') = functionPointer s arg in (s', v' : v, t ++ t', i ++ i')) (state, [], [], []) args
    -- state' = state {idCount = idCount state + 1}
    return (ExprResult (resultId, returnType), inst1, varInst, stackInst ++ [stackInst'])

handleConstructorSt :: DataType -> DataType -> [Variable] -> State LanxSt VeryImportantTuple
handleConstructorSt returnType functionType args =
  do
    (typeId, inst) <- generateTypeSt returnType
    returnId <- nextOpId -- handle type convert
    let stackInst = [returnedInstruction returnId (Asm.OpCompositeConstruct typeId (Asm.ShowList (map fst args)))]
    return (ExprResult (returnId, returnType), inst, [], stackInst)

handleExtractSt :: DataType -> [Int] -> Variable -> State LanxSt VeryImportantTuple
handleExtractSt returnType i var@(opId, _) =
  do
    (typeId, inst) <- generateTypeSt returnType
    returnId <- nextOpId
    let stackInst = [returnedInstruction returnId (Asm.OpCompositeExtract typeId opId (Asm.ShowList i))]
    return (ExprResult (returnId, returnType), inst, [], stackInst)

----- Below are stateless

handleOp' :: Ast.Op (L.Range, Type) -> ExprReturn
handleOp' op =
  let funcSign = case op of
        Ast.Plus _ -> (DT.DTypeUnknown, [DT.DTypeUnknown, DT.DTypeUnknown])
        Ast.Minus _ -> (DT.DTypeUnknown, [DT.DTypeUnknown])
        Ast.Times _ -> (DT.DTypeUnknown, [DT.DTypeUnknown, DT.DTypeUnknown])
        Ast.Divide _ -> (DT.DTypeUnknown, [DT.DTypeUnknown, DT.DTypeUnknown])
        Ast.Eq _ -> (DT.bool, [DT.DTypeUnknown, DT.DTypeUnknown])
        Ast.Neq _ -> (DT.bool, [DT.DTypeUnknown, DT.DTypeUnknown])
        Ast.Lt _ -> (DT.bool, [DT.DTypeUnknown, DT.DTypeUnknown])
        Ast.Le _ -> (DT.bool, [DT.DTypeUnknown, DT.DTypeUnknown])
        Ast.Gt _ -> (DT.bool, [DT.DTypeUnknown, DT.DTypeUnknown])
        Ast.Ge _ -> (DT.bool, [DT.DTypeUnknown, DT.DTypeUnknown])
        Ast.And _ -> (DT.DTypeUnknown, [DT.DTypeUnknown, DT.DTypeUnknown])
        Ast.Or _ -> (DT.DTypeUnknown, [DT.DTypeUnknown, DT.DTypeUnknown])
   in ExprApplication (OperatorFunction op) funcSign []

-----

generateExprSt :: Expr -> State LanxSt VeryImportantTuple
generateExprSt (Ast.EPar _ e) = generateExprSt e
generateExprSt (Ast.EBool _ x) = generateConstSt (Asm.LBool x)
generateExprSt (Ast.EInt _ x) = generateConstSt (Asm.LInt x)
generateExprSt (Ast.EFloat _ x) = generateConstSt (Asm.LFloat x)
generateExprSt (Ast.EList _ es) =
  do
    let len = length es
    let makeAssociative (a, b, c, d) = ([a], b, c, d)
    (results, inst, var, stackInst) <- foldMaplM (fmap makeAssociative . generateExprSt) es
    (typeId, typeInst) <- generateTypeSt (DT.DTypeArray len DT.DTypeUnknown)
    error "Not implemented array" -- TODO: EList
generateExprSt (Ast.EVar (_, t1) (Ast.Name (_, _) name)) =
  do
    state <- get
    let dType = typeConvert t1
    let maybeResult = findResult state (ResultVariableValue (env state, BS.unpack name, dType))
    case maybeResult of
      Just x -> return (x, mempty, [], [])
      Nothing ->
        case dType of
          DT.DTypeFunction returnType args -> handleVarFunctionSt (BS.unpack name) (returnType, args)
          _ ->
            do
              let ExprResult (varId, varType) = fromMaybe (error ("cant find var:" ++ show (env state, BS.unpack name, dType))) (findResult state (ResultVariable (env state, BS.unpack name, dType)))
              er <- insertResultSt (ResultVariableValue (env state, BS.unpack name, dType)) Nothing
              let ExprResult (valueId, _) = er
              searchTypeId_state2_varType <- gets (\s -> searchTypeId s varType) -- FIXME: please rename this
              let inst = returnedInstruction valueId (Asm.OpLoad searchTypeId_state2_varType varId)
              return (ExprResult (valueId, varType), mempty, [], [inst])
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
              functionType = DT.DTypeFunction returnType argTypes
           in case (length args', length argTypes) of
                (l, r) | l == r ->
                  case funcType of
                    CustomFunction id s -> applyFunctionSt id returnType args'
                    TypeConstructor t -> handleConstructorSt t functionType args'
                    TypeExtractor t int -> handleExtractSt t int (head args')
                    OperatorFunction op -> error "Not implemented" -- TODO:
                    FunctionFoldl -> error "Not implemented" -- TODO: eval foldl gen array length
                (l, r)
                  | l < r ->
                      -- uncompleted applicatoin
                      return $ (ExprApplication funcType (returnType, argTypes) args', mempty, [], [])
                (l, r) | l > r -> error "Too many arguments"
        _ -> error (show var1 ++ show var2)
    let finalVar = var3
    let inst' = inst1 +++ inst2 +++ inst3
    let varInst' = varInst1 ++ varInst2 ++ varInst3
    -- let stackInst' = stackInst1 ++ stackInst2 ++ stackInst3
    traceM (show (stackInst1, stackInst2, stackInst3))
    traceM (show (e1, e2))
    let stackInst' = stackInst1 ++ stackInst2 ++ stackInst3
    return (finalVar, inst', varInst', stackInst')
generateExprSt (Ast.EIfThenElse _ cond thenE elseE) =
  let
    getIdFromBool :: ExprReturn -> Asm.OpId
    getIdFromBool (ExprResult (id, DT.DTypeBool)) = id
    getIdFromBool _ = error "Expected bool"
   in
    do
      (_erCondResult, inst1, varInst1, stackInstCond) <- generateExprSt cond
      let conditionId = getIdFromBool _erCondResult
      (_erThen, inst2, varInst2, stackInstThen) <- generateExprSt thenE
      (_erElse, inst3, varInst3, stackInstElse) <- generateExprSt elseE
      let ExprResult (thenResultId, returnType) = _erThen
      let ExprResult (elseResultId, _rt') = _erElse
      -- when (returnType != _rt')
      --   error "type infer fucked up, then-branch-type is not same as else-branch-type"
      let varType = DT.DTypePointer Asm.Function returnType
      (varTypeId, inst4) <- generateTypeSt varType
      (varValueTypeId, inst5) <- generateTypeSt returnType

      opid_plus_1 <- nextOpId
      let (Asm.Id opid_plus_1_num) = opid_plus_1
      thenLabelId <- nextOpId
      elseLabelId <- nextOpId
      ifThenElseEndLabelId <- nextOpId
      finalReturnId <- nextOpId

      envs <- gets env
      _er <- insertResultSt (ResultVariable (envs, "ifThen" ++ show (opid_plus_1_num), returnType)) Nothing
      let (ExprResult (varId, _)) = _er

      let sInst' =
        -- sInst1'
            stackInstCond ++
            [noReturnInstruction $ Asm.OpSelectionMerge (ifThenElseEndLabelId) Asm.None] ++
            [noReturnInstruction $ Asm.OpBranchConditional conditionId (thenLabelId) (elseLabelId)] ++ 
        -- sInst2'
            [commentInstruction "then branch"] ++
            [returnedInstruction (thenLabelId) Asm.OpLabel] ++
            stackInstThen ++
            [noReturnInstruction $ Asm.OpStore varId thenResultId] ++
            [noReturnInstruction $ Asm.OpBranch (ifThenElseEndLabelId)] ++
        -- sInst3'
            [commentInstruction "else branch"] ++
            [returnedInstruction (elseLabelId) Asm.OpLabel] ++
            stackInstElse ++
            [noReturnInstruction $ Asm.OpStore varId elseResultId] ++
            [noReturnInstruction $ Asm.OpBranch (ifThenElseEndLabelId)] ++
        --
            [returnedInstruction (ifThenElseEndLabelId) Asm.OpLabel] ++
            [returnedInstruction (finalReturnId) $ Asm.OpLoad varValueTypeId varId]
      let varInst = varInst1 ++ varInst2 ++ varInst3 ++ [returnedInstruction varId $ Asm.OpVariable varTypeId Asm.Function]
      return (
        ExprResult (finalReturnId, returnType),
        inst1 +++ inst2 +++ inst3 +++ inst4 +++ inst5,
        varInst,
        sInst')
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
generateExprSt (Ast.EOp _ op) = do return (handleOp' op, mempty, [], [])
generateExprSt (Ast.ELetIn _ decs e) =
  do
    envs <- gets env
    modify (\s -> s{env = envs ++ [("letIn", DT.DTypeVoid)]})
    -- traceM (show decs)
    -- return $ error (show decs)
    (inst, varInst, stackInst) <- foldMaplM generateDecSt decs
    (result, inst1, varInst2, stackInst1) <- generateExprSt e
    modify (\s -> s{env = envs})
    return (result, inst +++ inst1, varInst ++ varInst2, stackInst ++ stackInst1)

-- in error (show (findResult state2 (ResultVariableValue (env state2, "x", envType))))
-- in error (show (idMap state2))
-- in error (show decs)

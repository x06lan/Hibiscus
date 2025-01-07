{-# LANGUAGE CPP #-}
{-# LANGUAGE NamedFieldPuns #-}

module Hibiscus.CodeGen where

import Control.Monad.State.Lazy
import qualified Data.ByteString.Lazy.Char8 as BS
import Data.List (find, intercalate)
import qualified Data.Map as Map
import Data.Maybe (fromJust, fromMaybe)
import Data.Monoid (First (..), getFirst)
import Data.STRef (newSTRef)
import qualified Hibiscus.Asm as Asm
import qualified Hibiscus.Ast as Ast
import Hibiscus.CodeGen.Constants (global)
import Hibiscus.CodeGen.GenExpr (
  generateExprSt,
  generateTypeSt,
  insertResultSt, applyExpr,
  findResultOrGenerateEntry,
  insertResult',
 )
import Hibiscus.CodeGen.Types
import Hibiscus.CodeGen.Type.DataType (DataType)
import qualified Hibiscus.CodeGen.Type.DataType as DT
import Hibiscus.CodeGen.Util (findDec, findResult, searchTypeId, getNameAndDType)
import qualified Hibiscus.TypeInfer as TI
import Hibiscus.Util (foldMaplM, foldMaprM)

generateInitSt :: Config -> [Dec] -> State LanxSt Instructions
generateInitSt cfg decs =
  do
    let startId = 0
    let headInstruction =
          HeaderFields
            { capabilityInst = Just $ noReturnInstruction $ Asm.OpCapability (capability cfg)
            , extensionInst = Just $ returnedInstruction (Asm.Id $ startId + 1) (Asm.OpExtInstImport (extension cfg))
            , memoryModelInst = Just $ noReturnInstruction $ Asm.OpMemoryModel (addressModel cfg) (memoryModel cfg)
            , entryPointInst = Nothing
            , executionModeInst = Just $ noReturnInstruction $ Asm.OpExecutionMode (Asm.IdName . entryPoint $ cfg) (executionMode cfg)
            , sourceInst = Just $ noReturnInstruction $ uncurry Asm.OpSource (source cfg)
            }
    put $
      LanxSt
        { idCount = startId + 1
        , idMap = Map.empty
        , env = [global]
        , decs = decs
        }
    _ <- insertResult' (ResultCustom "ext ") (ExprResult (Asm.Id 1, DT.DTypeVoid)) -- ext
    let inst =
          Instructions
            { headerFields = headInstruction
            , nameFields = [commentInstruction "Name fields"]
            , uniformsFields = [commentInstruction "uniform fields"]
            , typeFields = [commentInstruction "pe fields"]
            , constFields = [commentInstruction "Const fields"]
            , functionFields = []
            }
    return inst

generateUniformsSt_aux1 :: (String, DataType, Asm.StorageClass, Int) -> State LanxSt (Instructions, [Asm.ResultId])
generateUniformsSt_aux1 (name, dType, storage, location) =
  do
    (typeId, inst1) <- generateTypeSt (DT.DTypePointer storage dType)

    env_s1 <- gets env
    _er <- findResultOrGenerateEntry (ResultVariable (env_s1, name, dType))
    let ExprResult (id, _) = _er

    let variableInstruction = [returnedInstruction id (Asm.OpVariable typeId storage)]
    let nameInstruction = [noReturnInstruction (Asm.OpName id name)]
    let uniformsInstruction = [noReturnInstruction (Asm.OpDecorate id (Asm.Location location))]

    let inst1' =
          inst1
            { nameFields = nameFields inst1 ++ nameInstruction
            , uniformsFields = uniformsFields inst1 ++ uniformsInstruction
            , constFields = constFields inst1 ++ variableInstruction
            }
    return (inst1', [id]) -- it's a anti-optimised move, but making less mentally taxing

generateUniformsSt :: Config -> [Argument] -> State LanxSt Instructions
generateUniformsSt cfg args =
  let
    shaderTypeOfCfg = shaderType cfg
    entryPointOfCfg = entryPoint cfg
   in
    do
      let nntOfArgs = fmap getNameAndDType args
      let uniforms = (\((n, t), i) -> (n, t, Asm.Input, i)) <$> zip nntOfArgs [0 ..]
      let uniforms' = ("outColor", DT.vector4, Asm.Output, 0) : uniforms -- todo handle custom output
      (inst, ids) <- foldMaplM generateUniformsSt_aux1 uniforms'

      let hf = headerFields inst
      let hf' = hf{entryPointInst = Just $ noReturnInstruction (Asm.OpEntryPoint shaderTypeOfCfg (Asm.IdName entryPointOfCfg) entryPointOfCfg (Asm.ShowList ids))}
      let inst1 = inst{headerFields = hf'}

      return inst1

-- error (show (env state') ++ show uniforms')

generateMainFunctionSt :: Instructions -> Config -> Dec -> State LanxSt Instructions
generateMainFunctionSt inst cfg (Ast.Dec (_, t) (Ast.Name _ name) args e) =
  do
    let (returnType, argsType) = (DT.DTypeVoid, [])
    let functionType = DT.DTypeFunction returnType argsType

    (typeId, inst1) <- generateTypeSt functionType

    let funcId = Asm.IdName (BS.unpack name)
    insertResult' (ResultCustom "func ") (ExprResult (funcId, functionType))

    modify (\s -> s{env = global : [(BS.unpack name, functionType)]})
    labelId <- nextOpId

    inst2 <- generateUniformsSt cfg args
    (_er, inst3, varInst, exprInst) <- (generateExprSt e >>= applyExpr)
    let (ExprResult (resultId, _)) =  _er
    state5 <- get
    let returnTypeId = searchTypeId state5 returnType

    let ExprResult (varId, _) = fromMaybe (error $ show $ env state5) (findResult state5 (ResultVariable (env state5, "outColor", DT.vector4)))
    let saveInst = [noReturnInstruction (Asm.OpStore varId resultId)]

    let funcInst =
          FunctionInst
            { begin = [commentInstruction $ "function " ++ BS.unpack name, returnedInstruction funcId (Asm.OpFunction returnTypeId Asm.None typeId)]
            , parameter = []
            , label = [returnedInstruction labelId Asm.OpLabel]
            , variable = varInst
            , body = exprInst ++ saveInst ++ [noReturnInstruction Asm.OpReturn]
            , end = [noReturnInstruction Asm.OpFunctionEnd]
            }

    let inst4 = inst +++ inst1 +++ inst2 +++ inst3
    let inst5 = inst4{functionFields = functionFields inst4 ++ [funcInst]}
    return inst5

flattenFunctionInst :: FunctionInst -> [Asm.Instruction]
flattenFunctionInst func =
  let FunctionInst{begin, parameter, label, variable, body, end} = func
   in begin ++ parameter ++ label ++ variable ++ body ++ end

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
generate config decs = evalState aux noMatterState
  where
    noMatterState = undefined
    aux = do
      let mainDec = fromJust $ findDec decs (entryPoint config) DT.DTypeUnknown
      inst <- generateInitSt config decs
      inst' <- generateMainFunctionSt inst config mainDec
      -- (state3, _, inst2) = generateType initState (DTypePointer Input vector2)
      let finalInst = inst'
      return finalInst

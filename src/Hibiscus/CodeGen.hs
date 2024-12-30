{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-missing-signatures #-}

module Hibiscus.CodeGen where

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
import Hibiscus.CodeGen.GenExpr


generateInitSt :: Config -> [Dec] -> State LanxSt (Instructions)
generateInitSt cfg decs =
  do
    let startId = 0
    let headInstruction =
          HeaderFields
            { capabilityInst    = Just $ noReturnInstruction $ OpCapability (capability cfg)
            , extensionInst     = Just $ returnedInstruction (Id $ startId + 1) (OpExtInstImport (extension cfg))
            , memoryModelInst   = Just $ noReturnInstruction $ OpMemoryModel (addressModel cfg) (memoryModel cfg)
            , entryPointInst    = Nothing
            , executionModeInst = Just $ noReturnInstruction $ OpExecutionMode (IdName . entryPoint $ cfg) (executionMode cfg)
            , sourceInst        = Just $ noReturnInstruction $ uncurry OpSource (source cfg)
            }
    put $
      LanxSt
        { idCount = startId + 1
        , idMap = Map.empty
        , env = ([], DTypeVoid)
        , decs = decs
        }
    _ <- insertResultSt (ResultCustom "ext ") (Just (ExprResult (Id 1, DTypeVoid))) -- ext
    let inst =
          Instructions
            { headerFields   = headInstruction
            , nameFields     = [commentInstruction "Name fields"]
            , uniformsFields = [commentInstruction "uniform fields"]
            , typeFields     = [commentInstruction "Type fields"]
            , constFields    = [commentInstruction "Const fields"]
            , functionFields = []
            }
    return inst

generateUniformsSt_aux1 :: (String, DataType, StorageClass, Int) -> State LanxSt (Instructions, [ResultId])
generateUniformsSt_aux1 (name, dType, storage, location) =
  do
    (typeId, inst1) <- generateTypeSt (DTypePointer storage dType)

    env_s1 <- gets env
    _er <- insertResultSt (ResultVariable (env_s1, name, dType)) Nothing
    let ExprResult (id, _) = _er

    let variableInstruction = [returnedInstruction id (OpVariable typeId storage)]
    let nameInstruction     = [noReturnInstruction (OpName id name)]
    let uniformsInstruction = [noReturnInstruction (OpDecorate id (Location location))]

    let inst1' =
          inst1
            { nameFields     = nameFields inst1     ++ nameInstruction
            , uniformsFields = uniformsFields inst1 ++ uniformsInstruction
            , constFields    = constFields inst1    ++ variableInstruction
            }
    return (inst1', [id]) -- it's a anti-optimised move, but making less mentally taxing

generateUniformsSt :: Config -> [Argument] -> State LanxSt (Instructions)
generateUniformsSt cfg args =
  let
    shaderTypeOfCfg = shaderType cfg
    entryPointOfCfg = entryPoint cfg
   in
    do
      let nntOfArgs = fmap getNameAndDType args
      let uniforms = fmap (\((n, t), i) -> (n, t, Input, i)) $ zip nntOfArgs [0 ..]
      let uniforms' = ("outColor", vector4, Output, 0) : uniforms -- todo handle custom output
      (inst, ids) <- foldMaplM generateUniformsSt_aux1 uniforms'

      let hf = trace "test" $ headerFields inst
      let hf' = hf{entryPointInst = Just $ noReturnInstruction (OpEntryPoint shaderTypeOfCfg (IdName entryPointOfCfg) (entryPointOfCfg) (ShowList ids))}
      let inst1 = inst{headerFields = hf'}

      return inst1

-- error (show (env state') ++ show uniforms')

generateMainFunctionSt :: Instructions -> Config -> Dec -> State LanxSt Instructions
generateMainFunctionSt inst cfg (Ast.Dec (_, t) (Ast.Name (_, _) name) args e) =
  do
    let (returnType, argsType) = (DTypeVoid, [])
    let functionType = DTypeFunction returnType argsType

    (typeId, inst1) <- generateTypeSt functionType

    _er <- insertResultSt (ResultCustom "func ") (Just (ExprResult (IdName (BS.unpack name), functionType)))
    let ExprResult (funcId, _) = _er

    modify (\s -> s{idCount = idCount s + 1, env = ("":[BS.unpack name], functionType)})
    labelId <- gets (Id . idCount)

    inst2 <- generateUniformsSt cfg args
    (_er, inst3, varInst, exprInst) <- generateExprSt e
    let (ExprResult (resultId, _)) = _er
    state5 <- get
    let returnTypeId = searchTypeId state5 returnType

    let ExprResult (varId, _) = fromMaybe (error $ show $ env state5) (findResult state5 (ResultVariable (env state5, "outColor", vector4)))
    let saveInst = [noReturnInstruction (OpStore varId resultId)]

    let funcInst =
          FunctionInst
            { begin = [commentInstruction $ "function " ++ BS.unpack name, returnedInstruction (funcId) (OpFunction returnTypeId None typeId)]
            , parameter = []
            , label = [returnedInstruction labelId OpLabel]
            , variable = varInst
            , body = exprInst ++ saveInst ++ [noReturnInstruction OpReturn]
            , end = [noReturnInstruction OpFunctionEnd]
            }

    let inst4 = inst +++ inst1 +++ inst2 +++ inst3
    let inst5 = inst4{functionFields = functionFields inst4 ++ [funcInst]}
    return inst5

flattenFunctionInst :: FunctionInst -> [Instruction]
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
generate config decs =
  do
    let mainDec = fromJust $ findDec decs (entryPoint config) Nothing

    let noMatterState = undefined
    let (inst, initState) = runState (generateInitSt config decs) noMatterState
    let (inst', state') = runState (generateMainFunctionSt inst config mainDec) initState
    -- (state3, _, inst2) = generateType initState (DTypePointer Input vector2)

    let finalInst = inst'
    finalInst

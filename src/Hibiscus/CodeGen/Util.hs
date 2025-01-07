{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-missing-signatures #-}

module Hibiscus.CodeGen.Util where

import Control.Exception (handle)
import Hibiscus.CodeGen.Type.Builtin

-- type infer
import Control.Monad.State.Lazy
import qualified Data.ByteString.Lazy.Char8 as BS
import Data.List (find, intercalate)
import qualified Data.Map as Map
import Data.Monoid (First (..), getFirst)
import Data.STRef (newSTRef)
import Debug.Trace (trace)
import qualified Hibiscus.Asm as Asm
import qualified Hibiscus.Ast as Ast
import Hibiscus.CodeGen.Type.DataType (DataType)
import qualified Hibiscus.CodeGen.Type.DataType as DT
import Hibiscus.CodeGen.Types
import qualified Hibiscus.TypeInfer as TI
import Hibiscus.Util (foldMaplM, foldMaprM, replace)

findResult' :: ResultType -> ResultMap -> Maybe ExprReturn
findResult' (ResultVariable (envs, name, varType)) viIdMap =
  -- find variable up to the mother env
  let param = (viIdMap, name, varType)
   in getFirst (evalState (foldMaplM (aux param) envs) [])
 where
  aux :: (ResultMap, String, DataType) -> (String, DataType) -> State Env (First ExprReturn)
  aux (viIdMap, name, varType) env =
    do
      acc_env <- get
      let result = Map.lookup (ResultVariable (acc_env ++ [env], name, varType)) viIdMap

      put (acc_env ++ [env])
      return $ First result
findResult' (ResultVariableValue (envs, name, varType)) viIdMap =
  -- find variable up to the mother env
  let param = (viIdMap, name, varType)
   in getFirst (evalState (foldMaplM (aux param) envs) [])
 where
  aux :: (ResultMap, String, DataType) -> (String, DataType) -> State Env (First ExprReturn)
  aux (viIdMap, name, varType) env =
    do
      acc_env <- get
      let result = Map.lookup (ResultVariableValue (acc_env ++ [env], name, varType)) viIdMap
      put (acc_env ++ [env])
      return $ First result
findResult' key viIdMap = Map.lookup key viIdMap

findResult :: LanxSt -> ResultType -> Maybe ExprReturn
findResult s key =
  let viIdMap = idMap s -- very important idMap
   in findResult' key viIdMap

searchTypeId :: LanxSt -> DataType -> Asm.OpId
searchTypeId s dt =
  case findResult s (ResultDataType dt) of
    Just x -> case x of
      ExprResult (id, _) -> id
      _ -> error (show dt ++ " type not found")
    Nothing -> error (show dt ++ " type not found")

findDec' :: String -> DataType -> [Dec] -> Maybe Dec
findDec' name maybeFS = find' aux
 where
  aux = case maybeFS of
    DT.DTypeFunction argTs c ->
      ( \case
          Ast.Dec _ (Ast.Name _ n) args' _ ->
            let argTs' = map (typeConvert . TI.getType) args'
             in n == BS.pack name && argTs == argTs
          _ -> False
      )
    dType ->
      ( \case
          Ast.Dec _ (Ast.Name _ n) _ _ -> n == BS.pack name
          _ -> False
      )
  find' :: (a -> Bool) -> [a] -> Maybe a
  find' p xs =
    case filter p xs of
      [v] -> Just v
      [] -> Nothing
      -- TODO: to handle polymorphic function
      _ -> error "found multiple result, perhaps you want to use `find`"

-- search dec by name and function signature
findDec :: [Dec] -> String -> DataType -> Maybe Dec
findDec decs n mfs = findDec' n mfs decs

dtypeof :: Asm.Literal -> DataType
dtypeof (Asm.LBool _) = DT.bool
dtypeof (Asm.LUint _) = DT.uint32
dtypeof (Asm.LInt _) = DT.int32
dtypeof (Asm.LFloat _) = DT.float32

idNameOf :: Asm.Literal -> String
idNameOf l = case l of
  Asm.LBool b -> "bool_" ++ show b
  Asm.LUint u -> "uint_" ++ show u
  Asm.LInt i -> "int_" ++ show i
  Asm.LFloat f -> "float_" ++ replace '.' '_' (show f)

getNameAndDType :: Argument -> (String, DataType)
getNameAndDType (Ast.Argument (_, t) (Ast.Name _ name)) = (BS.unpack name, typeConvert t)

typeConvert :: Ast.Type () -> DataType
typeConvert t@(Ast.TVar _ (Ast.Name _ n)) =
  case getBuiltinType (BS.unpack n) of
    Just x -> x
    Nothing -> error ("Not implemented" ++ show t)
typeConvert (Ast.TPar _ t) = typeConvert t
typeConvert t@(Ast.TArrow _ t1 t2) =
  let
    processArrow :: Ast.Type () -> ([DataType], DataType)
    processArrow (Ast.TArrow _ t1' t2') =
      let (args, ret) = processArrow t2'
       in (typeConvert t1' : args, ret)
    processArrow t = ([], typeConvert t)

    (argTypes, returnType) = processArrow t
   in
    DT.DTypeFunction returnType argTypes
typeConvert (Ast.TApp _ t) = error ("Not implemented App" ++ show t)
typeConvert (Ast.TUnit _) = DT.DTypeVoid
typeConvert (Ast.TArray _ size t) = DT.DTypeArray size (typeConvert t)
typeConvert (Ast.TList _ t) = DT.DTypeLengthUnknownArray (typeConvert t)
typeConvert t = error ("Not implemented? " ++ show t)

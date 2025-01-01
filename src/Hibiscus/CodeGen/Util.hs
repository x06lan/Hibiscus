{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-missing-signatures #-}

module Hibiscus.CodeGen.Util where

import Control.Exception (handle)

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
import Hibiscus.CodeGen.Type
import Hibiscus.CodeGen.Type.DataType (DataType)
import qualified Hibiscus.CodeGen.Type.DataType as DT
import qualified Hibiscus.Type4plus as TI
import Hibiscus.Util (foldMaplM, foldMaprM)

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
searchTypeId s dt = case findResult s (ResultDataType dt) of
  Just x -> case x of
    ExprResult (id, _) -> id
    _ -> error (show dt ++ " type not found")
  Nothing -> error (show dt ++ " type not found")

findDec' :: String -> Maybe FunctionSignature -> [Dec] -> Maybe Dec
findDec' name maybeFS = find' aux
 where
  aux = case maybeFS of
    Nothing ->
      ( \case
          Ast.Dec _ (Ast.Name _ n) _ _ -> n == BS.pack name
          _ -> False
      )
    Just (_, argTs) ->
      ( \case
          Ast.Dec _ (Ast.Name _ n) args' _ ->
            let argTs' = map (DT.typeConvert . TI.getType) args'
             in n == BS.pack name && argTs == argTs
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
findDec :: [Dec] -> String -> Maybe FunctionSignature -> Maybe Dec
findDec decs n mfs = findDec' n mfs decs

{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-missing-signatures #-}

module Hibiscus.CodeGen.Util where

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
import Hibiscus.CodeGen.Type

import qualified Hibiscus.Type4plus as TI -- type infer

import Control.Monad.State.Lazy
import Data.Monoid (First (..), getFirst)

import Hibiscus.Util (foldMaplM, foldMaprM)


findResult' :: ResultType -> ResultMap -> Maybe ExprReturn
findResult' (ResultVariable ((envs, envType), name, varType)) viIdMap =
  -- find variable up to the mother env
  let param = (viIdMap, envType, name, varType)
   in getFirst . fst $ runState (foldMaplM (aux param) envs) []
 where
  aux :: (ResultMap, DataType, String, DataType) -> String -> State [String] (First ExprReturn)
  aux (viIdMap, envType, name, varType) env =
    do
      acc_env <- get
      let result = Map.lookup (ResultVariable ((acc_env ++ [env], envType), name, varType)) viIdMap
      put (acc_env ++ [env])
      return $ First result
findResult' (ResultVariableValue ((envs, envType), name, varType)) viIdMap =
  -- find variable up to the mother env
  let param = (viIdMap, envType, name, varType)
   in getFirst . fst $ runState (foldMaplM (aux param) envs) []
 where
  aux :: (ResultMap, DataType, String, DataType) -> String -> State [String] (First ExprReturn)
  aux (viIdMap, envType, name, varType) env =
    do
      acc_env <- get
      let result = Map.lookup (ResultVariableValue ((acc_env ++ [env], envType), name, varType)) viIdMap
      put (acc_env ++ [env])
      return $ First result
findResult' key viIdMap = Map.lookup key viIdMap

findResult :: LanxSt -> ResultType -> Maybe ExprReturn
findResult s key =
  let viIdMap = idMap s -- very important idMap
   in findResult' key viIdMap

searchTypeId :: LanxSt -> DataType -> OpId
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
            let argTs' = map (typeConvert . TI.getType) args'
             in n == BS.pack name && argTs == argTs
          _ -> False
      )
  find' :: (a -> Bool) -> [a] -> Maybe a
  find' p xs =
    case filter p xs of
      [v] -> Just v
      [] -> Nothing
      _ -> error "found multiple result, perhaps you want to use `find`"

-- search dec by name and function signature
findDec :: [Dec] -> String -> Maybe FunctionSignature -> Maybe Dec
findDec decs n mfs = findDec' n mfs decs

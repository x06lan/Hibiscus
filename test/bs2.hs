{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Eta reduce" #-}
module Main where

import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor (second)
import qualified Data.ByteString.Lazy.Char8 as BS
import Data.Foldable (foldlM, foldrM)
import Data.Map (Map)
import Data.Maybe (fromMaybe, maybe)

import Ast
import Lexer
import Parser
import System.Environment (getArgs)

type Result = Either String

type Symbol = Int
type Constraint a = (Name a, Type a)
type Env a = [Constraint a]

update :: (Show a) => Env a -> Constraint a -> Result (Env a)
update env x@(n, _) =
  case lookup n env of
    Just _ -> Left $ "Duplicated NAME" ++ show n
    Nothing -> return $ x : env

getNewSymbol :: (Show a) => Env a -> Name a -> Result (Env a, Type a)
getNewSymbol env name@(Name a _) =
  let
    extractIndex (_, TUnknown _ i) = i
    extractIndex _ = 0
    nextIndex = maximum (map extractIndex env) + 1
    t' = TUnknown a nextIndex
   in
    do
      e' <- update env (name, t')
      return (e', t')

getDecType :: (Show a) => Env a -> Dec a -> Result (Env a, Type a)
getDecType env_ (Dec a name args _) =
  do
    (e0, tb) <- getNewSymbol env_ name
    foldrM h (e0, tb) args
 where
  --  h :: Arg -> (Env, Type) -> Result (Env, Type)
  h (Argument md name) (e, tb) =
    do
      (e', ta) <- getNewSymbol e name
      return (e', TArrow md ta tb)
getDecType env _ = Left "Could only get type from Dec"

type Subst a = [(Symbol, Type a)]

subTy :: Subst a -> Type a -> Type a
subTy sub t@(TUnknown a s) = fromMaybe t (lookup s sub)
subTy _ t = t

subEnv :: Subst a -> Env a -> Env a
subEnv sub = map (second (subTy sub))

unify :: (Show a) => Env a -> Type a -> Type a -> Result (Subst a)
unify env t1 t2
  | t1 == t2 = return []
  | otherwise =
      case (t1, t2) of
        (TUnknown a s, t) -> return [(s, t)]
        (t, TUnknown a s) -> return [(s, t)]
        (TArrow _ a1 b1, TArrow _ a2 b2) -> do
          s1 <- unify env a1 a2
          s2 <- unify (subEnv s1 env) (subTy s1 b1) (subTy s1 b2)
          return $ s2 ++ s1
        _ -> Left $ "Cannot unify " ++ show t1 ++ " with " ++ show t2

-- foldrM :: (Foldable t, Monad m) => (a -> b -> m b) -> b -> t a -> m b
-- foldlM :: (Foldable t, Monad m) => (b -> a -> m b) -> b -> t a -> m b

typeCheck :: (Show a) => [Dec a] -> Result (Env a)
typeCheck decs_ = foldlM h [] decs_
 where
  --  h :: Env a -> Dec a -> Result (Env a)
  h env dec = case dec of
    (DecAnno _ n t) -> update env (n, t)
    (Dec a name args exp) ->
      do
        (e1, decT) <- getDecType env dec
        s2 <- maybe (return []) (unify e1 decT) (lookup name env)
        return (subEnv s2 e1)

main :: IO ()
main = do
  content <- BS.readFile "./example/test.hi"
  print $ typeCheck =<< runAlex content parseHibiscus

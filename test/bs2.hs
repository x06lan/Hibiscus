module Main where

import Control.Monad.State
import Control.Monad.Reader
import Data.Map (Map)
import Data.ByteString.Lazy.Char8 (ByteString, pack)

import Ast


type Result = Either String

type Constraint a = (Name a, Type a)
type Env a = [Constraint a]

update :: Show a => Env a -> Constraint a -> Result (Env a)
update env x@(n,_) =
  case lookup n env of
    Just _  -> Left $ "Duplicated NAME" ++ (show n)
    Nothing -> return $ x : env

getNewSymbol :: Show a => Env a -> Name a -> Result (Env a, Type a)
getNewSymbol env name@(Name a _) =
  let
    h (_, (TUnknown _ i)) = i
    h _                   = 0
    t' = TUnknown a $ (maximum $ map h env) + 1
  in do
    e' <- update env (name, t')
    return (e', t')

getDecType :: Show a => Env a -> Dec a -> Result (Env a, Type a)
getDecType env_ (Dec a name args _) = 
  do
    (e0, tb) <- getNewSymbol env_ name
    foldM h (e0, tb) args
  where
    h (e, tb) (Argument md name) =
      do
        (e', ta) <- getNewSymbol e name
        return (e', TArrow md ta tb)
getDecType env _ = undefined

unify :: Show a => Env a -> Type a -> Type a -> Result (Env a)
unify = undefined

typeCheck :: Show a => [Dec a] -> Result (Env a)
typeCheck decs_ = foldM h [] decs_
  where
--  h :: Env a -> Dec a -> Result (Env a)
    h env dec = case dec of
      (DecAnno _ n t)        -> update env (n, t)
      (Dec     a name args exp) ->
        do
          (e1, decT) <- getDecType env dec
          maybe (return e1) (unify e1 decT) (lookup name env)

main :: IO ()
main =
  do
    return ()

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
loookup :: Name a -> Env a -> Maybe (Type a)
loookup (Name _ n) = lookup n . map (\(Name _ n,t) -> (n,t))

update :: (Show a) => Env a -> Constraint a -> Result (Env a)
update env x@(n, _) =
  case lookup n env of
    Just _ -> Left $ "Duplicated " ++ show n
    Nothing -> return $ x : env

type Subst a = [(Symbol, Type a)]

getNewUnkTy :: (Show a) => Env a -> a -> Type a
getNewUnkTy env a =
  let
    extractIndex (_, TUnknown _ i) = i
    extractIndex _ = 0
    nextIndex = maximum (0 : map extractIndex env) + 1
  in
    TUnknown a nextIndex

getDecType :: (Show a) => Env a -> Dec a -> Result (Env a, Type a)
getDecType env_ (Dec a name args _) =
  let
    tb = getNewUnkTy env_ a
  in do
    foldrM h (env_, tb) args
  where
--  h :: Arg -> (Env, Type) -> Result (Env, Type)
    h (Argument a name) (e, tb) =
      let
        ta = getNewUnkTy e a
      in do
        e' <- update e (name, ta)
        return (e', TArrow a ta tb)
getDecType env _ = Left "Could only get type from Dec"

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

litType :: a -> String -> Type a
litType a str = TVar a $ Name a $ BS.pack str

typeInfer :: (Show a) => Env a -> Expr a -> Result (Subst a, Type a)
typeInfer env expr_ = case expr_ of
    EVar _ name@(Name _ x) ->
      case loookup name env of
        Just t  -> return ([], t)
        Nothing -> Left $ "Unbound variable: " ++ show x
    ELetIn a dec expr -> 
     do
       e0 <- typeCheck env [dec]
       typeInfer e0 expr
    EApp a f x ->
      do
        -- tf = tx -> tv
        (s1, tf) <- typeInfer env f -- FIXME: need subst
        (s2, tx) <- typeInfer (subEnv s1 env) x
        return (getNewUnkTy (subEnv (s1 ++ s2) env) a)
          >>= \tv ->
            unify env (subTy (s1 ++ s2) tf) (TArrow a tx tv)
              >>= \s3 ->
                return (s1 ++ s2 ++ s3, subTy (s1 ++ s2 ++ s3) tv)
    EBinOp a e1 op e2 -> return ([], getNewUnkTy env a) -- TODO: biop
    EOp a _ -> return ([], getNewUnkTy env a) -- TODO: op
    EPar _ exp -> typeInfer env exp
    EInt a _    -> return ([], litType a "Int"   )
    EFloat a _  -> return ([], litType a "Float" )
    EString a _ -> return ([], litType a "String")
    EUnit a     -> return ([], TUnit a           )
    x -> Left $ "WIP: unsupported structure: " ++ show x

typeCheck :: (Show a) => Env a -> [Dec a] -> Result (Env a)
typeCheck env_ decs_ = foldlM h env_ decs_
 where
  --  h :: Env a -> Dec a -> Result (Env a)
  h env dec = case dec of
    (DecAnno _ n t) -> case loookup n env of
        Just t' -> do
          s1 <- unify env t t'
          return (subEnv s1 env)
        Nothing -> update env (n, t)
    (Dec a name args expr) -> do
        (innerEnv, decT) <- getDecType env dec
        (eee, realT) <- case loookup name env of
          Just annT -> do
            s2 <- unify env decT annT
            return (subEnv s2 env, subTy s2 decT)
          Nothing -> update env (name, decT) >>= \e -> return (e, decT)
        (s2, t2) <- typeInfer innerEnv expr -- FIXME: need subst
        unify eee realT (TArrow a (getNewUnkTy eee a) t2)
        return eee

main :: IO ()
main = do
  content <- BS.readFile "./example/test.hi"
  print $                  runAlex content parseHibiscus
  print $ typeCheck [] =<< runAlex content parseHibiscus

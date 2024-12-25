{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Hibiscus.Type4plus where

import Hibiscus.Ast

import Data.Functor (void)
import Data.Bifunctor
import Data.ByteString.Lazy.Char8 (pack)
import Data.Foldable (foldlM, foldrM)
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Maybe (fromJust, fromMaybe)
import Data.Tuple (curry)
import Prelude hiding (lookup)

import GHC.Stack (HasCallStack)
import Debug.Trace (traceStack)

type TypeEnv = Map.Map (Name ()) (Type ()) 
type Subst = Map.Map MetaSymbol (Type ()) -- responsible to maintain all metas
type Context = (TypeEnv, Subst)

lookup :: (Name a) -> TypeEnv -> Maybe (Type ())
lookup n env = Map.lookup (void n) env

type Result = Either String
instance MonadFail Result where
  fail = Left

class Substable a where
  applySub :: Subst -> a -> a
instance Substable (Type ()) where
  applySub sub t@(TUnknown _ n) = fromMaybe t (Map.lookup n sub)
  applySub _ t = t

literalT :: String -> Type ()
literalT = TVar () . Name () . pack


bindVar :: MetaSymbol -> Type () -> Result Subst
bindVar v t = return $ Map.fromList [(v,t)]

unify :: HasCallStack => Type () -> Type () -> Result Subst
unify t1 t2
  | t1 == t2 = return mempty
  | otherwise = 
      traceStack ("unifying: " ++ show t1 ++ " ==? " ++ show t2) $ 
      case (t1, t2) of
        (TUnknown _ v, t) -> bindVar v t
        (t, TUnknown _ v) -> bindVar v t
        (TArrow _ t1 t2, TArrow _ t1' t2') -> do
          s1 <- unify t1 t1'
          s2 <- unify (applySub s1 t2) (applySub s1 t2')
          return (s1 <> s2)
        _ -> error $ "Cannot unify " ++ show t1 ++ " with " ++ show t2

freshTypeUnk :: Subst -> (Subst, Type ())
freshTypeUnk subs = (Map.fromList [(newSym, t')], t')
  where
    lastone = maximum $ [0] ++ Map.keys subs
    newSym = 1 + lastone
    t' = TUnknown () newSym

freshTypeUnk' :: Subst -> (Subst, Type ())
freshTypeUnk' s1 = (s2 <> s1, t')
    where
        (s2, t') = freshTypeUnk s1

(<><>) :: (Semigroup a , Semigroup b) => (a , b) -> (a , b) -> (a , b)
(a, b) <><> (a', b') = (a <> a', b <> b')

mcdonald :: Context -> Dec a -> Result Context
mcdonald jojo@(env, sub) dec =
  case dec of
    (DecAnno _ n_ t_) ->
      let
        n = void n_
        t = void t_
      in
      case lookup n env of
        Just t' -> do
          s1 <- unify t t'
          return $ (Map.fromList [(n, t)], s1) <><> jojo
        Nothing -> return $ (Map.fromList [(n, t)], mempty) <><> jojo
    (Dec a n _ _) ->
      case lookup n env of
        Just t -> return jojo
        Nothing -> let
            (s,t) = freshTypeUnk sub
            in return $ (Map.fromList [(void n, t)], s) <><> jojo

envFrom :: Context -> [Dec a] -> Result Context
envFrom = foldlM mcdonald

envFrom' :: [Dec a] -> Result Context
envFrom' = foldlM mcdonald (mempty, mempty)

addType :: (Functor f) => Type b -> f a -> f (a, Type b)
addType t = fmap (\a -> (a, t))
getType :: (Foldable f, Functor f) => f (a, Type b) -> Type b
getType = snd . foldr1 (\aa _ -> aa) -- XXX: IDK what exectly foldr1 do
forget :: (Functor f) => f (a, Type b) -> f a
forget = fmap fst

fmap2nd :: (Functor f) => (b -> b) -> f (a, b) -> f (a, b)
fmap2nd f = fmap (second f)

applySubM :: (Functor f) => Subst -> f (a, Type ()) -> f (a, Type ())
applySubM sub = fmap2nd (applySub sub)

magic :: Subst -> [Argument a] -> (Subst, [Argument (a, Type ())])
magic sub = foldr aux (mempty, [])
  where
    aux :: Argument a -> (Subst, [Argument (a, Type ())]) -> (Subst, [Argument (a, Type ())])
    aux arg (s1, args) =
      let
        (s2, t) = freshTypeUnk (s1 <> sub)
        arg' = addType t arg
      in 
        (s2 <> s1, arg' : args)

argToEnv :: [Argument (a, Type ())] -> TypeEnv
argToEnv = Map.fromList . map (\(Argument (_,t) n) -> (void n,t))


inferExpr :: Context -> Expr a -> Result (Subst, Expr (a, Type ()))
inferExpr ctx@(env,sub) expr = case expr of
  EInt _ _ -> return $ (mempty, addType (literalT "Int") expr)
  EFloat _ _ -> return $ (mempty, addType (literalT "Float") expr)
  EString _ _ -> return $ (mempty, addType (literalT "String") expr)
  EBool _ _ -> return $ (mempty, addType (literalT "Bool") expr)
  EUnit _ -> return $ (mempty, addType (literalT "Unit") expr)
  EPar _ e' -> inferExpr ctx e'
  EVar _ x -> case lookup x env of
    Nothing -> fail $ "Unbound variable: " ++ show x
    Just t -> return (mempty, addType t expr)
  ELetIn a decs body ->
    do
      ctx'@(e0, s0) <- envFrom ctx decs
      (s1, decs') <- inferDecs ctx' decs
      let ctx'' = (fmap (applySub s1) e0, s1 <> s0)
      (s2, body') <- inferExpr ctx'' body
      return (s2 <> s1, ELetIn (a, getType body') decs' body')
  EBinOp _ e1 _ e2 ->
    do
      (s1, e1') <- inferExpr ctx              e1
      (s2, e2') <- inferExpr (env, s1 <> sub) e2
      let t1 = getType e1'
      let t2 = getType e2'
      s3 <- unify t1 t2
      let finalSub = s3 <> s2 <> s1
      return (finalSub, addType (applySub s3 t1) expr)
    
  _ -> return (s1, addType t expr)
    where
      (s1, t) = freshTypeUnk sub


inferDecs :: Context -> [Dec a] -> Result (Subst, [Dec (a, Type ())])
inferDecs (env, sub) = foldlM aux (sub, [])
  where
    aux :: (Subst, [Dec (a, Type ())]) -> Dec a -> Result (Subst, [Dec (a, Type ())])
    aux (s0, decs) (Dec a name args body) = do
      let (s1, bodyType) = freshTypeUnk s0
      let (s2, argWithTypes) = magic (s1 <> s0) args
      let s210 = s2 <> s1 <> s0
      let funcType = foldr (TArrow ()) bodyType (map getType argWithTypes)
      let innerEnv = argToEnv argWithTypes
      (s4, body') <- inferExpr (innerEnv <> env, s210) body
      let bodyType' = getType body'
      s5 <- unify bodyType' bodyType
      let finalBody = applySubM s5 body'
      let funcType' = applySub (s5 <> s4 <> s210) funcType
      let finalArgs = map (applySubM (s5 <> s4 <> s210)) argWithTypes
      let finalName = addType (TUnit ()) name
      -- TODO: unify with annotation
      let finalSub = s5 <> s4 <> s210
      let finalDec = Dec (a, funcType') finalName finalArgs finalBody
      return (finalSub, finalDec : (map (applySubM finalSub) decs))
    
    -- Handle the case where the declaration is not defination
    aux microencourage _ = return microencourage

infer :: [Dec a] -> Result [Dec (a, Type ())]
infer decs = do
    ctx <- envFrom' decs
    (_, decs') <- inferDecs ctx decs
    return decs'

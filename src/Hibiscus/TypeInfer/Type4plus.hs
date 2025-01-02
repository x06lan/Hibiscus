{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Hibiscus.TypeInfer.Type4plus where

import Hibiscus.Ast

import Data.Functor (void)
import Data.Bifunctor
import Data.ByteString.Lazy.Char8 (pack)
import Data.Foldable (foldlM, foldrM)
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Maybe (fromJust, fromMaybe, listToMaybe)
import Data.Tuple (curry)
import Prelude hiding (lookup)

import GHC.Stack (HasCallStack)
import Debug.Trace hiding (trace)

import Hibiscus.TypeInfer.RSF

trace :: String -> a -> a
trace _ = id

type TypeEnv = Map.Map (Name ()) (Type ()) 
newtype Subst = Subst (Map.Map MetaSymbol (Type ())) deriving (Show) -- responsible to maintain all metas
type Context = (TypeEnv, Subst)

instance Semigroup Subst where
  s1@(Subst map1) <> (Subst map2) = Subst $ Map.map (applySub s1) map2 `Map.union` map1
instance Monoid Subst where
  mempty = Subst mempty
lookup :: (Name a) -> TypeEnv -> Maybe (Type ())
lookup n env = Map.lookup (void n) env

class Substable a where
  applySub :: Subst -> a -> a
instance Substable (Type ()) where
  applySub (Subst sub) t@(TUnknown _ n) = 
    trace ("applySub: " ++ show sub) $ 
    fromMaybe t (Map.lookup n sub)
  applySub s (TPar _ t) = applySub s t
  applySub s (TArrow _ ta tb) = TArrow () ta' tb'
    where
      ta' = applySub s ta
      tb' = applySub s tb
  applySub _ t = t

literalT :: String -> Type ()
literalT = TVar () . Name () . pack

unify :: HasCallStack => Type () -> Type () -> Result Subst
unify t1 t2
  | t1 == t2 = return mempty
  | otherwise =
    let
      bindVar :: MetaSymbol -> Type () -> Result Subst
      bindVar v t = return $ Subst $ Map.fromList [(v,t)]
    in
      trace ("unifying: " ++ show t1 ++ " ==? " ++ show t2) $ 
      case (t1, t2) of
        (TUnknown _ v, t) -> bindVar v t
        (t, TUnknown _ v) -> bindVar v t
        (TArrow _ t1 t2, TArrow _ t1' t2') -> do
          s1 <- unify t1 t1'
          s2 <- unify (applySub s1 t2) (applySub s1 t2')
          return (s1 <> s2)
        _ -> error $ "Cannot unify " ++ show t1 ++ " with " ++ show t2

unifyRS :: Type () -> Type () -> RSF e Subst ()
unifyRS t1 t2
  | t1 == t2 = return ()
  | otherwise =
    let
      bindVar :: MetaSymbol -> Type () -> RSF e Subst ()
      bindVar v t = do
        let newSub = Subst $ Map.fromList [(v, t)]
        modify (\s -> newSub <> s)
    in do
      traceM ("unifying: " ++ show t1 ++ " ==? " ++ show t2)
      case (t1, t2) of
        (TUnknown _ v, t) -> bindVar v t
        (t, TUnknown _ v) -> bindVar v t
        (TArrow _ t1 t2, TArrow _ t1' t2') -> do
          unifyRS t1 t1'
          s1 <- get
          unifyRS (applySub s1 t2) (applySub s1 t2')
        _ -> error $ "Cannot unify " ++ show t1 ++ " with " ++ show t2

freshTypeUnk :: Subst -> (Subst, Type ())
freshTypeUnk (Subst subs) = (Subst $ Map.fromList [(newSym, t')], t')
  where
    lastone = maximum $ [0] ++ Map.keys subs
    newSym = 1 + lastone
    t' = TUnknown () newSym

freshTypeUnk' :: Subst -> (Subst, Type ())
freshTypeUnk' s1 = (s2 <> s1, t')
    where
        (s2, t') = freshTypeUnk s1

freshTypeUnkRS :: RSF TypeEnv Subst (Type ())
freshTypeUnkRS =
  do
    lastnum <- gets (\(Subst s) -> maximum $ [0] ++ Map.keys s)
    let t' = 1 + lastnum
    let newSym = 1 + lastnum
    let t' = TUnknown () newSym
    let nm = Subst $ Map.fromList [(newSym, t')]
    modify (\s -> nm <> s)
    return t'

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
          return $ (Map.fromList [(n, t)], s1) <> jojo
        Nothing -> return $ (Map.fromList [(n, t)], mempty) <> jojo
    (Dec a n _ _) ->
      case lookup n env of
        Just t -> return jojo
        Nothing -> let
            (s,t) = freshTypeUnk sub
            in return $ (Map.fromList [(void n, t)], s) <> jojo

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

inferExprRS :: Expr a -> RSF TypeEnv Subst (Expr (a, Type ()))
inferExprRS e@(EInt _ _) = return $ addType (literalT "Int") e
inferExprRS e@(EFloat _ _) = return $ addType (literalT "Float") e
inferExprRS e@(EString _ _) = return $ addType (literalT "String") e
inferExprRS e@(EBool _ _) = return $ addType (literalT "Bool") e
inferExprRS e@(EUnit _) = return $ addType (literalT "Unit") e
inferExprRS (EPar _ e) = inferExprRS e
inferExprRS e@(EVar _ x) =
  do
    env <- ask
    case lookup x env of
      Nothing -> fail $ "Unbound variable: " ++ show x
      Just t -> return $ addType t e
inferExprRS (EList a exprs) =
    let
      -- aux :: Expr a -> (Subst, [Expr (a, Type ())]) -> Result (Subst, [Expr (a, Type ())])
      aux :: Expr a -> [Expr (a, Type ())] -> RSF TypeEnv Subst [Expr (a, Type ())]
      aux expr acc = do
        expr' <- inferExprRS expr
        s20 <- get
        -- check if type same as previous
        case acc of
          (x:_) -> unifyRS (getType x) (getType expr')
          []    -> modify id
        finalSub <- get
        return $ fmap (applySubM finalSub) (expr' : acc)
    in do
      exprs' <- foldrM aux [] exprs
      t <- maybe freshTypeUnkRS (return . getType) $ listToMaybe exprs'
      return $ EList (a, TList () t) exprs'
inferExprRS e =
  do
    s <- get
    env <- ask
    case inferExpr (env, s) e of
      Right (s', e') -> do
        put s'
        return e'
      Left e -> do
        fail e

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
  EList a exprs ->
    let
      aux :: Expr a -> (Subst, [Expr (a, Type ())]) -> Result (Subst, [Expr (a, Type ())])
      aux expr (s0, acc) = do
        (s2 , expr') <- inferExpr (env, s0) expr
        s3 <- case acc of
          (x:_) -> unify (getType x) (getType expr')
          []    -> return mempty
        let finalSub = s3 <> s2 <> s0
        return (finalSub, fmap (applySubM finalSub) (expr' : acc))
    in do
      (sub, exprs') <- foldrM aux (mempty, []) exprs
      let (s', t) = foldr (\x _ -> (sub, getType x)) (freshTypeUnk' sub) exprs'
      return (s', EList (a, TList () t) exprs')
  ELetIn a decs body ->
    do
      ctx'@(e0, s0) <- envFrom ctx decs
      (s1, decs') <- inferDecs ctx' decs
      let ctx'' = (fmap (applySub s1) e0, s1 <> s0)
      (s2, body') <- inferExpr ctx'' body
      return (s2 <> s1, ELetIn (a, getType body') decs' body')
  EApp a f x -> do
      -- tf = tx -> tv
      (s1, f') <- inferExpr ctx              f
      (s2, x') <- inferExpr (env, s1 <> sub) x
      let tf = getType f'
      let tx = getType x'
      let (s3, tv) = freshTypeUnk (s2 <> s1 <> sub)
      let s3210 = s3 <> s2 <> s1 <> sub
      s4 <- unify (applySub s3210 tf) (TArrow () tx tv)
      let s43210 = s4 <> s3210
      let finalEApp = EApp (a, applySub s4 tv) (applySubM s43210 f') (applySubM s43210 x')
      return (s43210, finalEApp)
  EBinOp a e1 biop e2 ->
    do
      (s1, e1') <- inferExpr ctx              e1
      (s2, e2') <- inferExpr (env, s1 <> sub) e2
      let t1 = getType e1'
      let t2 = getType e2'
      s3 <- unify t1 t2
      let eType = applySub s3 t1
      let finalType = if isBooleanOp biop then literalT "Bool" else eType
      let finalSub = s3 <> s2 <> s1
      return (finalSub, EBinOp (a,finalType) e1' (addType finalType biop) e2')
  EIfThenElse a condition thenE elseE -> do
    (s1, cond')  <- inferExpr ctx                    condition
    (s2, elseE') <- inferExpr (env, s1 <> sub)       elseE
    (s3, thenE') <- inferExpr (env, s1 <> s2 <> sub) thenE
    let s321 = s3 <> s2 <> s1
    s4 <- unify (applySub s321 $ getType cond') (literalT "Bool")
    s5 <- unify (applySub (s4 <> s321) $ getType elseE') (applySub (s4 <> s321) $ getType thenE')
    let finalSub = s5 <> s4 <> s321
    let finalCond = applySubM finalSub cond'
    let finalThen = applySubM finalSub thenE'
    let finalElse = applySubM finalSub elseE'
    let finalType = applySub finalSub $ getType elseE'
    return $ (finalSub, EIfThenElse (a, finalType) finalCond finalThen finalElse)
  _ -> return (s1, addType t expr)
      -- TODO: fold
    where
      (s1, t) = freshTypeUnk sub


inferDecs :: Context -> [Dec a] -> Result (Subst, [Dec (a, Type ())])
inferDecs (env, sub) = foldlM aux (sub, [])
  where
    aux :: (Subst, [Dec (a, Type ())]) -> Dec a -> Result (Subst, [Dec (a, Type ())])
    aux (s0, decs) (Dec a name args body) = do
      let (s1, bodyType) = freshTypeUnk s0
      let (s2, argWithTypes) = magic (s1 <> s0) args
      let s2s1s0 = s2 <> s1 <> s0
      let funcType = foldr (TArrow ()) bodyType (map getType argWithTypes)
      let innerEnv = argToEnv argWithTypes
      -- (s4, body') <- inferExpr (innerEnv <> env, s2s1s0) body
      (body', s4) <- runRSF (inferExprRS body) (innerEnv <> env) s2s1s0
      let bodyType' = getType body'
      s5 <- unify bodyType' bodyType
      let finalBody = applySubM s5 body'
      let funcType' = applySub (s5 <> s4 <> s2s1s0) funcType
      let prefinalType = applySub (s5 <> s4 <> s2s1s0) $ fromJust $ lookup name env
      s6 <- unify prefinalType funcType'
      let finalType = applySub s6 funcType'
      let finalArgs = map (applySubM (s6 <> s5 <> s4 <> s2s1s0)) argWithTypes
      let finalName = addType (TUnit ()) name
      let finalSub = s6 <> s5 <> s4 <> s2s1s0
      let finalDec = Dec (a, finalType) finalName finalArgs finalBody
      return (finalSub, map (applySubM finalSub) (finalDec : decs))
    aux microencourage _ = return microencourage

infer :: [Dec a] -> Result [Dec (a, Type ())]
infer decs = do
    ctx <- envFrom' decs
    (_, decs') <- inferDecs ctx decs
    return decs'

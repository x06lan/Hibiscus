{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use tuple-section" #-}
{-# HLINT ignore "Use const" #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# HLINT ignore "Monad law, left identity" #-}

module Hibiscus.Type2 (typeInfer) where

import Data.Functor (void)
import Data.Bifunctor
import Data.ByteString.Lazy.Char8 (pack)
import Data.Foldable (foldlM, foldrM)
import qualified Data.List as List
import Data.Maybe (fromJust, fromMaybe)
import Data.Tuple (curry)
import Data.Set (Set)
import Prelude hiding (lookup)

import Debug.Trace hiding (trace)
import GHC.Stack

import Hibiscus.Ast

trace :: String -> a -> a
trace _ = id

traceWith :: (a -> String) -> a -> a
traceWith f a = trace (f a) a

litType :: a -> String -> Type a
litType a = TVar a . Name a . pack

-- Types

type Result = Either String
instance MonadFail Result where
  fail = Left

type MetaCounter = Int
type Constraint = (MetaCounter, Set (Type ()))
type Context a = (Name a, Type a)
data Env a = Env MetaCounter [Context a] [Constraint] deriving (Show)

initialEnv = Env 0 [] []

data Subst a = Subst MetaCounter [(MetaCounter, Type a)] deriving (Show)

instance Semigroup (Subst a) where
  (Subst i1 xs1) <> (Subst i2 xs2) = Subst (max i1 i2) (xs1 ++ xs2)
instance Monoid (Subst a) where
  mempty = Subst 0 []

-- Lookup Methods

lookup :: Name a -> Env a -> Maybe (Type a)
lookup (Name _ n) (Env _ contexts _) = List.lookup n $ map (\(Name _ n, t) -> (n, t)) contexts

lookupBiop :: Op a -> Type a -> Result (Type a)
-- monoid operations
lookupBiop (Plus _)   t = return t
lookupBiop (Minus _)  t = return t
lookupBiop (Times _)  t = return t
lookupBiop (Divide _) t = return t
lookupBiop (And _)    t = return t
lookupBiop (Or _)     t = return t
-- boolean operations
lookupBiop _ _ = return $ litType undefined "Bool"

-- Rules

updateContext :: (Show a) => (Name a, Type a) -> Env a -> Result (Env a)
updateContext x@(n, _) (Env i contexts constraints) =
  case List.lookup n contexts of
    Just _ -> fail $ "Duplicated " ++ show n
    Nothing -> return $ Env i (x : contexts) constraints

newMeta' :: MetaCounter -> a -> (MetaCounter, Type a)
newMeta' i a = (i + 1, TUnknown a i)

newMeta :: Env a -> a -> (Subst a, Type a)
newMeta (Env i _ _) a = 
  let
    (i', t) = newMeta' i a
  in
    (Subst i' [], t)

-- Magics

liftSubstM :: (HasCallStack, Show a) => (Env a -> b -> Result (Subst a, c)) -> Env a -> b -> Result (Env a, c)
liftSubstM f env b = first (\s -> subEnv s env) <$> f env b

liftSubst :: (HasCallStack, Show a) => (Env a -> b -> (Subst a, c)) -> Env a -> b -> (Env a, c)
liftSubst f env b = first (\s -> subEnv s env) $ f env b

-- Helper: 

curryT :: Show a => a -> [Type a] -> Type a -> Type a
curryT a argTs tb = traceWith (\a -> "\nCURRY" ++ show a) $ foldr (TArrow a) tb argTs

getDecType :: (Show a) => Env a -> Dec a -> Result (Env a, Type a)
getDecType env_ (Dec a _ args _) =
  foldrM h (e0, tb) args
    where
      (e0, tb) = liftSubst newMeta env_ a
      h (Argument a name) (e, tb) =
        do
          let (e', ta) = liftSubst newMeta e a
          e'' <- updateContext (name, ta) e'
          return (e'', TArrow a ta tb)
getDecType env _ = fail "Could only get type from Dec"

-- Helper: Subsutions

subTy :: (Show a) => Subst a -> Type a -> Type a
subTy (Subst _ sub) t@(TUnknown _ s) =
  let
    traceMsg = "SubT: " ++ show sub ++ " on " ++ show t
   in
    trace traceMsg $ fromMaybe t (List.lookup s sub)
subTy sub t@(TArrow a ta tb) = TArrow a (subTy sub ta) (subTy sub tb)
subTy _ t = t

subEnv :: (Show a) => Subst a -> Env a -> Env a
subEnv sub@(Subst i' _) env@(Env i x y) =
  let
    traceMsg = "SubE: " ++ show sub
    envMap f (Env i xs ys) = Env i (f xs) ys
   in
    trace traceMsg $ envMap (List.map $ second $ subTy sub) $ Env (max i i') x y

-- Helper: Type Markers

addType :: (Functor f) => Type a -> f a -> f (a, Type a)
addType t = fmap (\a -> (a, t))

getType :: (Foldable f, Functor f) => f (a, Type a) -> Type a
getType = snd . foldr1 (\aa _ -> aa) -- XXX: IDK what exectly foldr1 do

forget :: (Functor f) => f (a, Type a) -> f a
forget = fmap fst

fmap2nd :: (Functor f) => (b -> b) -> f (a, b) -> f (a, b)
fmap2nd f = fmap (second f)

-- Main Functions

unify :: Show a => Env a -> Type a -> Type a -> Result (Subst a, Type a)
unify env@(Env i contexts constraints) t1 t2
  | t1 == t2 = return (mempty, t1)
  | otherwise =
      case (t1, t2) of
        (TUnknown a s, t) -> return (Subst 0 [(s,t)], t)
        (t, TUnknown a s) -> return (Subst 0 [(s,t)], t)
        (TArrow a a1 b1, TArrow _ a2 b2) -> do
          (s1, ta) <- unify env b1 b2
          (s2, tb)  <- unify (subEnv s1 env) (subTy s1 a1) (subTy s1 a2)
          return (s1 <> s2, TArrow a ta tb)
        _ -> fail $ "Cannot unify " ++ show t1 ++ " with " ++ show t2

inferExpr :: (Show a) => Env a -> Expr a -> Result (Subst a, Expr (a, Type a))
inferExpr env expr_ = case expr_ of
  EVar a name@(Name _ x) ->
    case lookup name env of
      Just t -> return (mempty, addType t expr_)
      Nothing -> traceStack "UUU:" $ fail $ "Unbound variable: " ++ show name
  ELetIn a decs expr ->
    do
      (innerEnv, decs') <- traceWith (\d -> "LETIN: " ++ show d) $ inferDec env decs
      (s1, expr') <- inferExpr innerEnv expr
      return (s1, ELetIn (a, getType expr') decs' expr')
  EApp a f x ->
    do
      -- tf = tx -> tv
      (s1, f') <- inferExpr env             f
      (s2, x') <- inferExpr (subEnv s1 env) x
      let tf = getType f'
      let tx = getType x'
      let (s2', tv) = newMeta (subEnv (s1 <> s2) env) a
      (s3, _) <- trace (">: " ++ show expr_) $ unify (subEnv (s1 <> s2 <> s2') env) (subTy (s1 <> s2 <> s2') tf) (TArrow a tx tv)
      let s9 = s1 <> s2 <> s2' <> s3
      -- FIXME: works now but I guess some duplicated symbel problem here
      let eapp' = traceWith (\t -> "<: " ++ show t) $ EApp (a, (subTy s9 tv)) (fmap2nd (subTy s9) f') (fmap2nd (subTy s9) x')
      return (s9, eapp')
  EBinOp a exp1 op exp2 ->
    do
      (s1, exp1') <- inferExpr env             exp1
      (s2, exp2') <- inferExpr (subEnv s1 env) exp2
      let t1 =            getType exp1'
      let t2 = subTy s2 $ getType exp1'
      let env0 = subEnv (s1 <> s2) env
      (s3, operatedType) <- unify env0 t1 t2
      resultType <- lookupBiop op operatedType
      let ebinop' = EBinOp (a, resultType) exp1' (addType (TUnit a) op) exp2'
      return (s1 <> s2 <> s3, ebinop')
  EOp a op ->
    do
      let (s1, t) = newMeta env a
      let t' = TArrow a t t
      let eop' = EOp (a, t') (addType (TUnit a) op)
      return (s1, eop')
  EPar _ exp -> inferExpr env exp
  EInt a _ -> return (mempty, addType (litType a "Int") expr_)
  EFloat a _ -> return (mempty, addType (litType a "Float") expr_)
  EString a _ -> return (mempty, addType (litType a "String") expr_)
  EUnit a -> return (mempty, addType (TUnit a) expr_)
  x -> fail $ "WIP: unsupported structure: " ++ show x

inferDec :: (HasCallStack, Show a) => Env a -> [Dec a] -> Result (Env a, [Dec (a, Type a)])
inferDec env_ = foldlM aux (env_, [])
 where
  aux (env@(Env i contexts constraints), acc) dec = case dec of
    (DecAnno _ n t) ->
      case lookup n env of
        Just t' -> do
          (s1, _) <- unify env t t'
          return (subEnv s1 env, acc)
        Nothing -> updateContext (n, t) env >>= \e -> return (e, acc)
    (Dec a name args expr) ->
      do
        (innerEnv@(Env i' _ constraints'), decT) <- getDecType env dec
        
        -- update from arguments
        let e0 = Env i' contexts constraints'

        -- check if the type is already annotated
        (e0', s0, uniT) <-
          case lookup name e0 of
            Just t -> do
              (s', u') <- unify e0 decT t
              return (subEnv s' e0, s', u')
            Nothing -> do
              e0'' <- updateContext (name, decT) e0
              return (e0'', mempty, decT)

        -- TODO: updateContext  

        -- inner unify
        let innerEnv' = subEnv s0 innerEnv
        (s1, expr') <- inferExpr innerEnv' expr
        let ie' = subEnv s1 innerEnv'

        let args' = List.map (\arg -> addType (seriousGetType ie' arg) arg) args
        let uniT' = subTy (s0 <> s1) uniT'
        let dec' = Dec (a, uniT) (addType (TUnit a) name) args' expr'
        
        return (subEnv (s0 <> s1) e0', dec' : acc)
     where
      seriousGetType eeee (Argument _ n) = fromJust $ lookup n eeee

typeInfer :: Show a => [Dec a] -> Result (Env a, [Dec (a, Type a)])
typeInfer = inferDec initialEnv
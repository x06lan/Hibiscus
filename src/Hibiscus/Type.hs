{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use tuple-section" #-}
{-# HLINT ignore "Use const" #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# HLINT ignore "Monad law, left identity" #-}

module Hibiscus.Type (typeInfer) where

import Data.Bifunctor
import Data.ByteString.Lazy.Char8 (pack)
import Data.Foldable (foldlM, foldrM)
import qualified Data.List as List
import Data.Maybe (fromJust, fromMaybe)
import Data.Tuple (curry)
import Prelude hiding (lookup)

-- import Debug.Trace
import GHC.Stack

import Hibiscus.Ast

trace :: String -> a -> a
trace _ = id
traceWith :: (a -> String) -> a -> a
traceWith f a = trace (f a) a

litType :: a -> String -> Type a
litType a str = TVar a $ Name a $ pack str

type Result = Either String

instance MonadFail Result where
  fail = Left

type Symbol = Int

type Constraint a = (Name a, Type a)
data Env a = Env Symbol [Constraint a] deriving (Show)

empty = Env 0 []

envMap :: ([Constraint a] -> [Constraint a]) -> Env a -> Env a
envMap f (Env i xs) = Env i (f xs)

lookup :: Name a -> Env a -> Maybe (Type a)
lookup (Name _ n) (Env _ xs) = List.lookup n $ map (\(Name _ n, t) -> (n, t)) xs

update :: (Show a) => Env a -> Constraint a -> Result (Env a)
update (Env i es) x@(n, _) =
  case List.lookup n es of
    Just _ -> fail $ "Duplicated " ++ show n
    Nothing -> return $ Env i $ x : es

data Subst a = Subst Symbol [(Symbol, Type a)] deriving (Show)

instance Semigroup (Subst a) where
  (Subst i1 xs1) <> (Subst i2 xs2) = Subst (max i1 i2) (xs1 ++ xs2)
instance Monoid (Subst a) where
  mempty = Subst 0 []

-- NOTE: helpers to mark type info
addType :: (Functor f) => Type a -> f a -> f (a, Type a)
addType t = fmap (\a -> (a, t))

getType :: (Foldable f, Functor f) => f (a, Type a) -> Type a
getType = snd . foldr1 (\aa _ -> aa) -- XXX: IDK what exectly foldr1 do

forget :: (Functor f) => f (a, Type a) -> f a
forget = fmap fst

fmapType :: (Functor f) => (Type a -> Type a) -> f (a, Type a) -> f (a, Type a)
fmapType f = fmap (second f)

-- NOTE: I guess this is too power to haskell ;;
-- type BiResult a b = Result (a, b)
-- instance Bifunctor BiResult where
--   bimap f g = fmap (bimap f g)
-- liftSubstM :: (Bifunctor f) => (Env a -> b -> f (Subst a) c) -> Env a -> b -> f (Env a) c
-- liftSubstM f env b = first (\s -> subEnv s env) $ f env b

liftSubstM :: (HasCallStack, Show a) => (Env a -> b -> Result (Subst a, c)) -> Env a -> b -> Result (Env a, c)
liftSubstM f env b = first (\s -> subEnv s env) <$> f env b

liftSubst :: (HasCallStack, Show a) => (Env a -> b -> (Subst a, c)) -> Env a -> b -> (Env a, c)
liftSubst f env b = first (\s -> subEnv s env) $ f env b

getNewUnknownType :: Env a -> a -> (Subst a, Type a)
getNewUnknownType (Env i xs) a = (Subst (i + 1) [], TUnknown a i)

curryT :: a -> [Type a] -> Type a -> Type a
curryT a argTs tb = traceWith (\a -> "\nCURRY" ++ show a) $ foldr (TArrow a) tb argTs

getDecType :: (Show a) => Env a -> Dec a -> Result (Env a, Type a)
getDecType env_ (Dec a name args _) =
  let
    (e0, tb) = liftSubst getNewUnknownType env_ a
   in
    do
      foldrM h (e0, tb) args
 where
  --  h :: Arg -> (Env, Type) -> Result (Env, Type)
  h (Argument a name) (e, tb) =
    let
      (e', ta) = liftSubst getNewUnknownType e a
     in
      do
        e'' <- update e' (name, ta)
        return (e'', TArrow a ta tb)
getDecType env _ = fail "Could only get type from Dec"

subTy :: Subst a -> Type a -> Type a
subTy (Subst _ sub) t@(TUnknown _ s) =
  let
    traceMsg = "SubT: " ++ show sub ++ " on " ++ show t
   in
    trace traceMsg $ fromMaybe t (List.lookup s sub)
subTy sub t@(TArrow a ta tb) = TArrow a (subTy sub ta) (subTy sub tb)
subTy _ t = t

subEnv :: (Show a) => Subst a -> Env a -> Env a
subEnv sub@(Subst i' _) env@(Env i xs) =
  let
    traceMsg = "SubE: " ++ show sub
   in
    trace traceMsg $ envMap (map $ second $ subTy sub) (Env (max i i') xs)

unify :: (HasCallStack, Show a) => Env a -> Type a -> Type a -> Result (Subst a)
unify env t1 t2
  | t1 == t2 = return mempty
  | otherwise =
      case (t1, t2) of
        (TUnknown a s, t) -> return $ Subst 0 [(s, t)]
        (t, TUnknown a s) -> return $ Subst 0 [(s, t)]
        (TArrow _ a1 b1, TArrow _ a2 b2) -> do
          s1 <- unify env b1 b2
          s2 <- unify (subEnv s1 env) (subTy s1 a1) (subTy s1 a2)
          return $ s1 <> s2
        _ -> do
          -- errorWithStackTrace $ (prettyCallStack callStack) ++"\n"++ show env ++ "\nCannot unify " ++ show t1 ++ " with " ++ show t2
          fail $ "Cannot unify " ++ show t1 ++ " with " ++ show t2

inferExpr :: (HasCallStack, Show a) => Env a -> Expr a -> Result (Subst a, Expr (a, Type a))
inferExpr env expr_ = case expr_ of
  EVar a name@(Name _ x) ->
    case lookup name env of
      Just t -> return (mempty, addType t expr_)
      Nothing -> fail $ "Unbound variable: " ++ show name
  ELetIn a decs expr ->
    do
      (env0, decs') <- inferDec env decs
      (s1, expr') <- inferExpr env0 expr
      return (s1, ELetIn (a, getType expr') decs' expr')
  EApp a f x ->
    do
      -- tf = tx -> tv
      (s1, f') <- inferExpr env f
      (s2, x') <- inferExpr (subEnv s1 env) x
      let tf = traceWith (\t -> "TF: " ++ show f' ++ " : " ++ show t) $ getType f'
      let tx = traceWith (\t -> "TX: " ++ show x' ++ " : " ++ show t) $ getType x'
      return (getNewUnknownType (traceWith (\a -> "EA: " ++ show a) $ subEnv (s1 <> s2) env) a)
        >>= \(s2', tv) ->
          trace ("APPPPPPP: " ++ show expr_) $
            unify (subEnv (s1 <> s2 <> s2') env) (traceWith (\a -> "unifyleft: " ++ show a) $ subTy (s1 <> s2 <> s2') tf) (traceWith (\a -> "unifyright: " ++ show a) $ TArrow a tx tv) -- ASDFGHJK
              >>= \s3 -> do
                -- traceShow (prettyT tf) (pure ())
                -- FIXME: works now but I guess some duplicated symbel problem here
                return (s1 <> s2 <> s2' <> s3, EApp (a, subTy (s1 <> s2 <> s2' <> s3) tv) f' x')
  EBinOp a e1 op e2 ->
    -- TODO: biop
    let
      (s', t) = getNewUnknownType env a
     in
      return (s', addType t expr_)
  -- EOp a f -> -- TODO: op
  --   do
  --     tf <- lookup f env
  --     return ([], addType tf expr_)
  EPar _ exp -> inferExpr env exp
  EInt a _ -> return (mempty, addType (litType a "Int") expr_)
  EFloat a _ -> return (mempty, addType (litType a "Float") expr_)
  EString a _ -> return (mempty, addType (litType a "String") expr_)
  EUnit a -> return (mempty, addType (TUnit a) expr_)
  x -> fail $ "WIP: unsupported structure: " ++ show x

inferDec :: (HasCallStack, Show a) => Env a -> [Dec a] -> Result (Env a, [Dec (a, Type a)])
inferDec env_ = foldlM aux (env_, [])
 where
  aux (env@(Env m e0s), acc) dec = case dec of
    (DecAnno _ n t) ->
      case lookup n env of
        Just t' -> do
          s1 <- unify env t t'
          return (subEnv s1 env, acc)
        Nothing -> update env (n, t) >>= \e -> return (e, acc)
    (Dec a name args expr) ->
      do
        (innerEnv@(Env m' _), decT) <- getDecType env dec
        let e0 = Env m' e0s

        (e0, uniT) <-
          case lookup name e0 of
            Just t -> do
              s1 <- unify e0 decT t
              return (subEnv s1 e0, subTy s1 decT)
            Nothing ->
              update e0 (name, decT) >>= \e -> return (e, decT)

        (s1, expr') <- inferExpr innerEnv expr
        let ie' = subEnv s1 innerEnv
        let unknownFunctionT = curryT a (map (seriousGetType ie') args) (getType expr')
        s2 <- unify ie' uniT unknownFunctionT

        let args' = map (\arg -> addType (seriousGetType ie' arg) arg) args
        let dec' = Dec (a, getType expr') (addType (subTy s2 uniT) name) args' expr'

        return (subEnv (s1 <> s2) e0, dec' : acc)
     where
      seriousGetType eeee (Argument _ n) = fromJust $ lookup n eeee

typeInfer :: (HasCallStack, Show a) => [Dec a] -> Result (Env a, [Dec (a, Type a)])
typeInfer = inferDec empty

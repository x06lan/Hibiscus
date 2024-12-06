{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Hibiscus.Type where

import Data.Bifunctor (second)
import Data.ByteString.Lazy.Char8 (pack)
import Data.Foldable (foldlM, foldrM)
import Data.Maybe (fromJust, fromMaybe)
-- import Debug.Trace
-- import GHC.Stack

import Hibiscus.Ast

type Result = Either String

instance MonadFail (Result) where
  fail = Left

type Symbol = Int
type Constraint a = (Name a, Type a)
data Env a = Env Symbol [Constraint a] deriving (Show)

empty = Env 0 []
envMap :: ([Constraint a] -> [Constraint a]) -> Env a -> Env a
envMap f (Env i xs) = Env i (f xs)

loookup :: Name a -> Env a -> Maybe (Type a)
loookup (Name _ n) (Env _ xs)= lookup n $ map (\(Name _ n,t) -> (n,t)) xs

update :: (Show a) => Env a -> Constraint a -> Result (Env a)
update (Env i es) x@(n, _) =
  case lookup n es of
    Just _ -> fail $ "Duplicated " ++ show n
    Nothing -> return $ Env i $ x : es

type Subst a = [(Symbol, Type a)]

getNewUnkTy :: Env a -> a -> (Env a, Type a)
getNewUnkTy (Env i xs) a = (Env (i + 1) xs, TUnknown a i)
curryT :: a -> [Type a] -> Type a -> Type a
curryT a argTs tb = foldr (TArrow a) tb argTs

getDecType :: (Show a) => Env a -> Dec a -> Result (Env a, Type a)
getDecType env_ (Dec a name args _) =
  let
    (e0, tb) = getNewUnkTy env_ a
  in do
    foldrM h (e0, tb) args
  where
--  h :: Arg -> (Env, Type) -> Result (Env, Type)
    h (Argument a name) (e, tb) =
      let
        (e', ta) = getNewUnkTy e a
      in do
        e'' <- update e' (name, ta)
        return (e'', TArrow a ta tb)
getDecType env _ = fail "Could only get type from Dec"

subTy :: Subst a -> Type a -> Type a
subTy sub t@(TUnknown _ s)   = fromMaybe t (lookup s sub)
subTy sub t@(TArrow a ta tb) = TArrow a (subTy sub ta) (subTy sub tb)
subTy _ t = t

subEnv :: Subst a -> Env a -> Env a
subEnv sub = envMap $ map $ second $ subTy sub
--           envMap  (map  (second  (subTy   sub)))

unify :: (Show a) => Env a -> Type a -> Type a -> Result (Subst a)
unify env t1 t2
  | t1 == t2 = return []
  | otherwise =
      case (t1, t2) of
        (TUnknown a s, t) -> return [(s, t)]
        (t, TUnknown a s) -> return [(s, t)]
        (TArrow _ a1 b1, TArrow _ a2 b2) -> do
          s1 <- unify env b1 b2
          s2 <- unify (subEnv s1 env) (subTy s1 a1) (subTy s1 a2)
          return $ s1 ++ s2
--          fail $ "AAAA: " ++ show t1 ++ show t2 ++ show s1 ++ show s2
        _ -> fail $ "Cannot unify " ++ show t1 ++ " with " ++ show t2

-- foldrM :: (Foldable t, Monad m) => (a -> b -> m b) -> b -> t a -> m b
-- foldlM :: (Foldable t, Monad m) => (b -> a -> m b) -> b -> t a -> m b

litType :: a -> String -> Type a
litType a str = TVar a $ Name a $ pack str

class (Foldable f, Functor f) => Danceparty f where
  {-# MINIMAL tellCompilerAutoInstance #-}
  tellCompilerAutoInstance :: f a -> ()
  addType :: Type a -> f a -> f (a, Type a)
  addType t = fmap (\a -> (a, t))
  forget :: f (a, Type a) -> f a
  forget = fmap (\(a, t) -> a)
  getType :: f (a, Type a) -> Type a
  getType = snd . foldr1 (\aa bb -> bb) -- XXX: IDK what exectly foldr1 do
instance Danceparty Expr where
  tellCompilerAutoInstance _ = ()
instance Danceparty Dec where
  tellCompilerAutoInstance _ = ()
instance Danceparty Argument where
  tellCompilerAutoInstance _ = ()
instance Danceparty Name where
  tellCompilerAutoInstance _ = ()

inferExpr :: (Show a) => Env a -> Expr a -> Result (Subst a, Expr (a, Type a))
inferExpr env expr_ = case expr_ of
  EVar a name@(Name _ x) ->
    case loookup name env of
      Just t  -> return ([], addType t expr_)
      Nothing -> fail $ "Unbound variable: " ++ show name
  ELetIn a decs expr -> 
    do
      (env0, decs') <- inferDec env decs
      (s1, expr') <- inferExpr env0 expr
      return (s1, ELetIn (a, getType expr') decs' expr')
  EApp a f x ->
    do
      -- tf = tx -> tv
      (s1, f') <- inferExpr            env  f
      (s2, x') <- inferExpr (subEnv s1 env) x
      let tf = getType f'
      let tx = getType x'
      return (getNewUnkTy (subEnv (s1 ++ s2) env) a)
        >>= \(e0, tv) ->
          unify e0 (subTy s2 tf) (TArrow a tx tv)
            >>= \s3 -> do
              -- traceShow (prettyT tf) (pure ())
              -- FIXME: works now but I guess some duplicated symbel problem here
              return (s1 ++ s2 ++ s3, EApp (a, subTy (s1 ++ s2 ++ s3) tv) f' x')
  -- EBinOp a e1 op e2 -> -- TODO: biop
  --   let
  --     (e', t) = getNewUnkTy env a
  --   in
  --     return ([], addType t expr_)
  -- EOp a f -> -- TODO: op
  --   do
  --     tf <- lookup f env
  --     return ([], addType tf expr_)
  EPar _ exp -> inferExpr env exp
  EInt a _    -> return ([], addType (litType a "Int"   ) expr_)
  EFloat a _  -> return ([], addType (litType a "Float" ) expr_)
  EString a _ -> return ([], addType (litType a "String") expr_)
  EUnit a     -> return ([], addType (TUnit a           ) expr_)
  x -> fail $ "WIP: unsupported structure: " ++ show x

-- typeCheck :: (Show a) => Env a -> Dec a -> Result (Env a)
-- typeCheck env dec = case dec of
--   (DecAnno _ n t) ->
--     case loookup n env of
--       Just t' -> do
--         s1 <- unify env t t'
--         return (subEnv s1 env)
--       Nothing -> update env (n, t)
--   (Dec a name args expr) ->
--     do
--       (innerEnv, decT') <- getDecType env dec
--       (e0, decT) <-
--         case loookup name env of
--           Just annT -> do
--             s1 <- unify env decT' annT
--             return (subEnv s1 env, subTy s1 decT')
--           Nothing ->
--             update env (name, decT') >>= \e -> return (e, decT')
--       (s2, texp) <- inferExpr innerEnv expr
--       ie' <- return $ subEnv s2 innerEnv
-- --        (ie',t3) <- return $ getNewUnkTy (subEnv s2 innerEnv) a
--       s3 <- unify ie' decT (curryT a (map (\(Argument _ n) -> fromJust $ loookup n ie') args) texp)
--       return $ subEnv (s2 ++ s3) e0

-- doSmthAboutType :: (Show a) => [Dec a] -> Result (Env a)
-- doSmthAboutType = foldlM typeCheck empty

inferDec :: (Show a) => Env a -> [Dec a] -> Result (Env a, [Dec (a, Type a)])
inferDec env_ decs_ = foldlM h (env_,[]) decs_
 where
  h (env, acc) dec = case dec of
    (DecAnno _ n t) ->
      case loookup n env of
        Just t' -> do
          s1 <- unify env t t'
          return (subEnv s1 env, acc)
        Nothing -> update env (n, t) >>= \e -> return (e, acc)
    (Dec a name args expr) ->
      do
        (innerEnv, decT) <- getDecType env dec
        (e0, uniT) <-
          case loookup name env of
            Just t -> do
              s1 <- unify env decT t
              return (subEnv s1 env, subTy s1 decT)
            Nothing ->
              update env (name, decT) >>= \e -> return (e, decT)
        (s1, expr') <- inferExpr innerEnv expr
        ie' <- return $ subEnv s1 innerEnv
        let seriousGetType eeee (Argument _ n) = fromJust $ loookup n eeee
        s2 <- unify ie' uniT (curryT a (map (seriousGetType ie') args) $ getType expr')
        let dec' = Dec (a, getType expr') (addType uniT name) (map (\ar -> addType (seriousGetType ie' ar) ar) args) expr'
        return $ (subEnv (s1 ++ s2) e0, dec' : acc)

typeInfer' :: (Show a) => [Dec a] -> Result (Env a, [Dec (a, Type a)])
typeInfer' = inferDec empty

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

{-# HLINT ignore "Eta reduce" #-}
module Main where

import Data.Bifunctor (second)
import Data.Maybe
import qualified Data.ByteString.Lazy.Char8 as BS
import Data.Foldable (foldlM, foldrM)
import Data.Map (Map)
import Data.Maybe (fromMaybe, maybe)

import Debug.Trace

import Ast
import Lexer
import Parser
import System.Environment (getArgs)

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
litType a str = TVar a $ Name a $ BS.pack str

typeInfer :: (Show a) => Env a -> Expr a -> Result (Subst a, Type a)
typeInfer env expr_ = case expr_ of
    EVar _ name@(Name _ x) ->
      case loookup name env of
        Just t  -> return ([], t)
        Nothing -> fail $ "Unbound variable: " ++ show name
    ELetIn a dec expr -> 
     do
       e0 <- typeCheck env [dec]
       typeInfer e0 expr
    EApp a f x ->
      do
        -- tf = tx -> tv
        (s1, tf) <- typeInfer            env  f
        (s2, tx) <- typeInfer (subEnv s1 env) x
        return (getNewUnkTy (subEnv (s1 ++ s2) env) a)
          >>= \(e0, tv) ->
            unify e0 (subTy s2 tf) (TArrow a tx tv)
              >>= \s3 -> do
                -- traceShow (prettyT tf) (pure ())
                -- FIXME: works now but I guess some duplicated symbel problem here
                return (s1 ++ s2 ++ s3, subTy s3 tv)
    EBinOp a e1 op e2 -> -- TODO: biop
      let
        (e', t) = getNewUnkTy env a
      in
        return ([], t)
    EOp a _ -> -- TODO: op
      let
        (e', t) = getNewUnkTy env a
      in
        return ([], t)
    EPar _ exp -> typeInfer env exp
    EInt a _    -> return ([], litType a "Int"   )
    EFloat a _  -> return ([], litType a "Float" )
    EString a _ -> return ([], litType a "String")
    EUnit a     -> return ([], TUnit a           )
    x -> fail $ "WIP: unsupported structure: " ++ show x

typeCheck :: (Show a) => Env a -> [Dec a] -> Result (Env a)
typeCheck env_ decs_ = foldlM h env_ decs_
 where
  --  h :: Env a -> Dec a -> Result (Env a)
  h env dec = case dec of
    (DecAnno _ n t) ->
      case loookup n env of
        Just t' -> do
          s1 <- unify env t t'
          return (subEnv s1 env)
        Nothing -> update env (n, t)
    (Dec a name args expr) ->
      do
        (innerEnv, decT') <- getDecType env dec
        (e0, decT) <-
          case loookup name env of
            Just annT -> do
              s1 <- unify env decT' annT
              return (subEnv s1 env, subTy s1 decT')
            Nothing ->
              update env (name, decT') >>= \e -> return (e, decT')
        (s2, texp) <- typeInfer innerEnv expr
        ie' <- return $ subEnv s2 innerEnv
--        (ie',t3) <- return $ getNewUnkTy (subEnv s2 innerEnv) a
        s3 <- unify ie' decT (curryT a (map (\(Argument _ n) -> fromJust $ loookup n ie') args) texp)
        return $ subEnv (s2 ++ s3) e0

main :: IO ()
main = do
  putStrLn "\n----- Parse Result ---------------"
  content <- BS.readFile "./example/test.hi"
  print $                     runAlex content parseHibiscus
  putStrLn "\n----- Infer Result ---------------"
  print $ typeCheck empty =<< runAlex content parseHibiscus

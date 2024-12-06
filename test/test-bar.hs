-- XXX: I GIVE THIS UP, but I believe it still valuable
module Main where

import Control.Monad.State
import Control.Monad.Reader

import Data.Map (Map)
import Data.ByteString.Lazy.Char8 (ByteString, pack)

import Ast

-- an example from https://github.com/jykuo-love-shiritori/Hibiscus/issues/2

data UT = UT deriving (Show)

-- type Env a = Map String (Type a)

-- unify :: Env a -> Env a -> [Dec a] -> [Dec a]
-- unify _ _ [] = []
-- unify tenv env ((Dec _ name arg mt exp):xs) = undefined
-- --  where
-- --   h (TVar a n) = undefined
-- --   h _ = undefined
-- u1 :: Env a -> Env a -> Expr a -> Expr a
-- u1 tenv env exp = undefined
--  where
--   h ELetIn _ dec exp = undefined
--   h EInt _ itg = undefined
--   h _ = undefined

-- type Env a = Map String (Type a)
type Poo a = Maybe (Type a)
type Constraint a = (Name a, Poo a)
type Env a = [Constraint a]

----- AUXILIARYS BEGIN -----
type Symbol = Int
getNewSymbol :: Env a -> Name a -> (Env a, Type a)
getNewSymbol env name@(Name a _) = (ne, nt)
 where
  h acc (_, TUnknown _ i) = max acc i
  h acc _              = acc
  ns = 1 + foldl h 0 env
  nt = TUnknown a ns
  ne = (name, nt) : env

-- md := metadata
curry :: Env a -> [Argument a] -> Type a -> Either String (Env a, Type a)
curry env args t = foldr h (env, t) args
 where
   h (e,t) (Argument md name) = (ne, TArrow a nt t)
    where
      (ne, nt) = getNewSymbol e name
    

class Puff f where
  getConstraints :: Env a -> f a -> Env a

instance Puff Dec where
  getConstraints env dec = case dec of
    (DecAnno _ n t)      -> [(n, t)]
    (Dec     a n args _) -> [(n, curry ne args nt)]
     where
       (ne, nt) = getNewSymbol e name
instance Puff Argument where
  getConstraints env (Argument a name) = [(name, )]
   where
     (ne, nt) = getNewSymbol e name

litType :: a -> String -> Type a
litType a str = TVar a $ Name a $ pack str
----- AUXILIARYS END -------

type Subst a = [(Symbol, Type a)]  -- Substitution map

unify :: Show a => Type a -> Type a -> Either String (Subst a)
unify t1 t2
  | t1 == t2 = return []
  | otherwise =
    case (t1, t2) of
      (TVar _ n, t) -> bind n t
      (t, TVar _ n) -> bind n t
      (TArrow _ l1 r1, TArrow _ l2 r2) -> do
          s1 <- unify l1 l2
          s2 <- unify (applySubst s1 r1) (applySubst s1 r2)
          return (s1 ++ s2)
      _ -> Left $ "Cannot unify " ++ show t1 ++ " with " ++ show t2
  where
    bind :: Name a -> Type a -> Either String (Subst a)
    bind = undefined
--    bind v t
--        | t == TVar v = return []
--        | v `occursIn` t = Left $ "Occurs check failed: " ++ v ++ " in " ++ show t
--        | otherwise = return [(v, t)]
--    
--    occursIn :: String -> Type -> Bool
--    occursIn v TInt = False
--    occursIn v TBool = False
--    occursIn v (TVar v') = v == v'
--    occursIn v (TFun t1 t2) = occursIn v t1 || occursIn v t2

type Infer a = State Int a

freshTypeVar :: String -> Infer (Type UT)
freshTypeVar = undefined
--freshTypeVar prefix = do
--    n <- get
--    put (n + 1)
--    return $ TVar UT (prefix ++ show n)

applySubstEnv = undefined
applySubst = undefined

typeInfer' :: Show a => Env a -> Expr a -> (Env a, Expr a)
typeInfer' = undefined

typeInfer :: Show a => Env a -> Expr a -> Either String (Subst a, Type a)
typeInfer env expr_ = case expr_ of
    EVar _ name@(Name _ x) ->
      case lookup name env of --FIXME: look upd need rewrite
        Just t  -> return ([], t)
 	Nothing -> Left $ "Unbound variable: " ++ show x
    ELetIn _ (Dec _ name args decexp) exp ->
      let
        argEnv = concatMap getConstraints args
      in do
        (s1, t1) <- typeInfer (env ++ argEnv) decexp
        (s2, t2) <- typeInfer (env ++ [(name, t1)]) exp
        return (s1 ++ s2, t2)
    EApp a f x -> do
        -- tf = tx -> tv
        (s1, tf) <- typeInfer env f
        (s2, tx) <- typeInfer (applySubstEnv s1 env) x
        tv <- undefined -- TODO: get new type var
        s3 <- unify (applySubst s2 tf) (TArrow a tx tv)
        return (s3 ++ s2 ++ s1, applySubst s3 tv)
    EInt a _    -> return ([], litType a "Int")
    EFloat a _  -> return ([], litType a "Float")
    EString a _ -> return ([], litType a "String")
    EPar _ exp -> typeInfer env exp
    EUnit a -> return ([], TUnit a)
    _ -> Left "WIP: unsupported structure"

--traverse :: Applicative f => (a -> f b) -> t a -> f (t b)
--
typeCheck' :: Show a => [Dec a] -> State (Env a) (Either String (Env a))
typeCheck' decs_ = foldl h (return []) decs_
  where
    h :: Either String (Env a) -> Dec a -> Either String (Env a)
    h = undefined

typeCheck :: Show a => [Dec a] -> [Either String (Dec a)]
typeCheck decs_ = fmap h decs_
  where
    toplevelEnv = concatMap getConstraints decs_
    h env (Dec a name args exp) =
      let
        argEnv = concatMap getConstraints args
	t0 = case lookup n toplevelEnv of
	  Just t  -> t
	  Nothing -> undefined
      in do
        (s1, t1) <- typeInfer (argEnv ++ toplevelEnv) exp
        s2 <- unify t0 t1
        return (Dec a name args exp)
    h decAnno = return decAnno

main :: IO ()
main =
--  let
--    rs = testDecs >>= typeCheck
--  in
  do
--    putStrLn ("aaa" ++ (show rs))
    return ()


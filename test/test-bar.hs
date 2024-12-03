module Main where

import Data.Map (Map)
import Control.Monad.State

import Parser

-- an example from https://github.com/jykuo-love-shiritori/Hibiscus/issues/2

data UT
  = UT
  deriving (Show)

-- let the_answer : int =
--   let a = 20 in
--   let b = 1 in
--   let c = 2 in
--   a * c + b * c
-- let main (unit : ()) : () =
--   print ("The answer is: " + the_answer)

testDecs = Right
  [ Dec UT (Name UT "the_answer") [] (Just (TVar UT (Name UT "int")))
    (ELetIn UT (Dec UT (Name UT "a") [] Nothing (EInt UT 20))
      (ELetIn UT (Dec UT (Name UT "b") [] Nothing (EInt UT 1))
        (ELetIn UT (Dec UT (Name UT "c") [] Nothing (EInt UT 2))
          (EBinOp UT
            (EBinOp UT
              (EVar UT (Name UT "a"))
              (Times UT)
              (EVar UT (Name UT "c")))
            (Plus UT)
            (EBinOp UT
              (EVar UT (Name UT "b"))
              (Times UT)
              (EVar UT (Name UT "c")))))))
  , Dec UT (Name UT "main") [Argument UT (Name UT "unit") (Just (TUnit UT))] (Just (TUnit UT))
    (EApp UT
      (EVar UT (Name UT "print"))
      (EPar UT
        (EBinOp UT
          (EString UT "\"The answer is: \"")
          (Plus UT)
          (EVar UT (Name UT "the_answer")))))
  ]

-- type Env a = Map String (Type a)

-- unify :: TyEnv a -> Env a -> [Dec a] -> [Dec a]
-- unify _ _ [] = []
-- unify tenv env ((Dec _ name arg mt exp):xs) = undefined
-- --  where
-- --   h (TVar a n) = undefined
-- --   h _ = undefined
-- u1 :: TyEnv a -> Env a -> Exp a -> Exp a
-- u1 tenv env exp = undefined
--  where
--   h ELetIn _ dec exp = undefined
--   h EInt _ itg = undefined
--   h _ = undefined

-- type TyEnv a = Map String (Type a)

type TyEnv a = [(Name a, Type a)]
--lookup = undefined

-- chatGPT gens

type Subst a = [(String, Type a)]  -- Substitution map

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

-- get new type symbol
newST = undefined


typeInfer :: Show a => TyEnv a -> Exp a -> Either String (Subst a, Type a)
typeInfer env expr_ = case expr_ of
    EVar _ name@(Name _ x) -> case lookup name env of
        Just t -> return ([], t)
        Nothing -> Left $ "Unbound variable: " ++ x
    ELetIn _ (Dec _ name args maybetype decexp) exp ->
      let
        aux arg = case arg of
          (Argument a n Nothing)  -> (n, TVar a n)
          (Argument _ n (Just t)) -> (n, t)
      in let
        argenv = foldl (\e a -> e ++ [aux a]) env args
      in do
        (s1, t1) <- typeInfer argenv decexp
        (s2, t2) <- typeInfer (env ++ [(name, t1)]) exp
        return (s1 ++ s2, t2)
    EApp _ f x -> do
        -- tf = tx -> tv
        (s1, tf) <- typeInfer env f
        (s2, tx) <- typeInfer (applySubstEnv s1 env) x
        tv <- undefined -- TODO: get new type var
        s3 <- unify (applySubst s2 tf) (TArrow undefined tx tv)
        return (s3 ++ s2 ++ s1, applySubst s3 tv)
    EInt _ _ -> return ([], TLit "int")
    EPar _ exp -> typeInfer env exp
    EUnit a -> return ([], TUnit a)
    _ -> Left "WIP: unsupported structure"

--
--traverse :: Applicative f => (a -> f b) -> t a -> f (t b)

typeCheck :: Show a => [Dec a] -> Either String [Dec a]
typeCheck decs_ = traverse h decs_
  where
    h_dec (Dec a n _ Nothing _)  = (n, TVar a n)
    h_dec (Dec _ n _ (Just t) _) = (n, t)
    -- toplevelEnv = foldl (\e d -> e ++ [h_dec d]) [] decs_
    toplevelEnv = undefined

    h_arg arg = case arg of
      (Argument a n Nothing)  -> (n, TVar a n)
      (Argument _ n (Just t)) -> (n, t)
    getargenv = foldl (\e a -> e ++ [h_arg a]) []

    h :: Show a => Dec a -> Either String (Dec a)
    h (Dec a n args maybety exp) =
      let
        argenv = getargenv args
      in do
        (s1, t1) <- typeInfer (argenv ++ toplevelEnv) exp
        s2 <- undefined
        return (Dec a n args (Just t1) exp)

main :: IO ()
main = let
    rs = testDecs >>= typeCheck
  in do
  putStrLn ("aaa" ++ (show rs))
  return ()


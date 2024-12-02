module Main where

import Data.Map (Map)
import Control.Monad.State

import Parser

-- an example from https://github.com/jykuo-love-shiritori/Hibiscus/issues/2

data UT = UT | NUT String -- Unknown Type

-- let the_answer : int =
--   let a = 20 in
--   let b = 1 in
--   let c = 2 in
--   a * c + b * c
-- let main (unit : ()) : () =
--   print ("The answer is: " + the_answer)

test = Right
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

type TyEnv a = [(String, Type a)]
--lookup = undefined

-- chatGPT gens

type Subst a = [(String, Type a)]  -- Substitution map

unify :: Type a -> Type a -> Either String (Subst a)
unify = undefined
--unify t1 t2 = case (t1, t2) of
--    (TInt, TInt) -> return []
--    (TBool, TBool) -> return []
--    (TVar v, t) -> bind v t
--    (t, TVar v) -> bind v t
--    (TFun l1 r1, TFun l2 r2) -> do
--        s1 <- unify l1 l2
--        s2 <- unify (applySubst s1 r1) (applySubst s1 r2)
--        return (s1 ++ s2)
--    _ -> Left $ "Cannot unify " ++ show t1 ++ " with " ++ show t2
--  where
--    bind :: String -> Type -> Either String Subst
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

typeInfer :: TyEnv a -> Exp a -> Either String (Subst a, Type a)
typeInfer env expr_ = case expr_ of
    ELetIn _ (Dec _ _ _ _ _) exp -> undefined
    EVar _ (Name _ x) -> case lookup x env of
        Just t -> return ([], t)
        Nothing -> Left $ "Unbound variable: " ++ x
    EApp _ f x -> do
        (s1, t1) <- typeInfer env f
        (s2, t2) <- typeInfer (applySubstEnv s1 env) x
        tv <- undefined
        s3 <- unify (applySubst s2 t1) (TArrow undefined t2 tv)
        return (s3 ++ s2 ++ s1, applySubst s3 tv)
    EInt _ _ -> return ([], TLit "int")
    EPar _ exp -> typeInfer env exp
    _ -> Left "WIP: unsupported structure"

main = do
  return ()


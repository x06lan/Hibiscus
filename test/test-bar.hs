module Main where

import Parser

import Data.Map (Map)

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
    (EBinOp UT (EBinOp UT (EVar UT (Name UT "a")) (Times UT) (EVar UT (Name UT "c"))) (Plus UT) (EBinOp UT (EVar UT (Name UT "b")) (Times UT) (EVar UT (Name UT "c")))))))
  , Dec UT (Name UT "main") [Argument UT (Name UT "unit") (Just (TUnit UT))] (Just (TUnit UT))
    (EApp UT (EVar UT (Name UT "print")) (EPar UT (EBinOp UT (EString UT "\"The answer is: \"") (Plus UT) (EVar UT (Name UT "the_answer")))))
  ]

type TyEnv a = Map String (Type a)

unify :: TyEnv a -> [Dec a] -> [Dec a]
unify _ [] = []
unify env (x:xs) = undefined

main = do
  return ()


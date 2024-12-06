module Main where

import System.Exit

import Hibiscus.Type (typeInfer')
import Hibiscus.Ast

-- testAst from:
-- Vec4 :: Float -> Float -> Float -> Float -> Vec4 
-- main x y = Vec4 x y 1.0 1.0;
-- f n =
--     let
--         v = 1;
--     in
--         n + v;
-- l = 12;
testAst = [DecAnno () (Name () "Vec4") (TArrow () (TVar () (Name () "Float")) (TArrow () (TVar () (Name () "Float")) (TArrow () (TVar () (Name () "Float")) (TArrow () (TVar () (Name () "Float")) (TVar () (Name () "Vec4")))))),Dec () (Name () "main") [Argument () (Name () "x"),Argument () (Name () "y")] (EApp () (EApp () (EApp () (EApp () (EVar () (Name () "Vec4")) (EVar () (Name () "x"))) (EVar () (Name () "y"))) (EFloat () 1.0)) (EFloat () 1.0)),Dec () (Name () "f") [Argument () (Name () "n")] (ELetIn () (Dec () (Name () "v") [] (EInt () 1)) (EBinOp () (EVar () (Name () "n")) (Plus ()) (EVar () (Name () "v")))),Dec () (Name () "l") [] (EInt () 12)]

main :: IO ()
main =
    case typeInfer' testAst of
        Right (_, es) -> mapM_ print es
        Left err -> die err

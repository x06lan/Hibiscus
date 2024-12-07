module Main where

import Asm
import Ast
import CodeGen
import qualified Data.ByteString.Lazy.Char8 as BS
import Inference
import Lexer (runAlex)
import Parser (parseHibiscus)
import System.Environment (getArgs)
import Typing

main :: IO ()
main = do
  -- putStrLn "\n----- Parse Result ---------------"
  content <- BS.readFile "./example/test.hi"
  -- print $ runAlex content parseHibiscus
  -- putStrLn "\n----- Infer Result ---------------"
  let maybe_type = typeCheck empty =<< runAlex content parseHibiscus
  let type_ast = case maybe_type of
        Left err -> error err
        Right l -> l

  print $ runAlex content parseHibiscus
  print type_ast

-- let test =case type_ast of
--   Left err -> putStrLn err
--   Right type_ast ->
-- putStrLn (foldl (\acc x -> acc ++ "\n" ++ show x) "" type_ast)

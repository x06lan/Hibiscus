module Main where

import qualified Data.ByteString.Lazy.Char8 as BS
import Lexer (runAlex)
import Parser (parseHibiscus)
import System.Environment (getArgs)
import Ast
import Typing
import Asm
import CodeGen
import Inference


main :: IO ()
main = do
  putStrLn "\n----- Parse Result ---------------"
  content <- BS.readFile "./example/test.hi"
  print $ runAlex content parseHibiscus
  putStrLn "\n----- Infer Result ---------------"
  print $ typeCheck empty =<< runAlex content parseHibiscus

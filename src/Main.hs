module Main where

import qualified Data.ByteString.Lazy.Char8 as BS
import Lexer (runAlex)
import Parser (parseHibiscus)
import System.Environment (getArgs)
import Ast
import Typing
import Asm
import CodeGen


main :: IO ()
main = do
    args <- getArgs
    content <- BS.readFile $ head args
    let ast = case runAlex content parseHibiscus of
            Left err -> error err
            Right ast -> ast
    let result = CodeGen.genCode CodeGen.defaultConfig ast

    let instructions = headerFields result ++  nameFields result ++ uniformsFields result ++ constFields result ++ functionFields result
    
    let lines = foldl (\acc x -> acc ++ show x ++"\n") "" instructions

    writeFile "out.asm" lines



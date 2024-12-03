module Main where

import qualified Data.ByteString.Lazy.Char8 as BS
import Lexer (runAlex)
import Parser (parseHibiscus)
import System.Environment (getArgs)

main :: IO ()
main = do
    args <- getArgs
    content <- BS.readFile $ head args
    print $ runAlex content parseHibiscus

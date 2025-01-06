module Main where

import System.Exit

import qualified Data.ByteString.Lazy.Char8 as BS
import Data.Either (fromRight)
import Hibiscus.CodeGen (generate)
import Hibiscus.CodeGen.Constants (defaultConfig)
import Hibiscus.Parsing.Lexer (runAlex)
import Hibiscus.Parsing.Parser (parseHibiscus)
import Hibiscus.TypeInfer (infer)
import System.Environment (getArgs)

main :: IO ()
main = do
  content <- BS.readFile "test/test.hi"
  let parseResult = fromRight (error "parse error") $ runAlex content parseHibiscus
  let inferResult = fromRight (error "infer error") $ infer parseResult
  let asmResult = generate defaultConfig inferResult
  print parseResult
  print inferResult
  print asmResult
  return ()

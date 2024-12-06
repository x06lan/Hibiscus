module Main where

import qualified Data.ByteString.Lazy.Char8 as BS
import Hibiscus.Lexer (runAlex)
import Hibiscus.Parser (parseHibiscus)
import Hibiscus.Type (doSmthAboutType)
import System.Environment (getArgs)
import Control.Monad (when)

main :: IO ()
main = do
  args <- getArgs
  when (null args) $ error "Usage: program <file-path>"
  let inputFilePath = head args
  
  putStrLn "\n----- Parse Result ---------------"
  content <- BS.readFile inputFilePath
  case runAlex content parseHibiscus of
    Left err -> putStrLn $ "Parse Error: " ++ err
    Right parseResult -> do
      print parseResult
      putStrLn "\n----- Type Check Result ---------------"
      case doSmthAboutType parseResult of
        Left err -> putStrLn $ "Check Error: " ++ err
        Right inferResult -> print inferResult

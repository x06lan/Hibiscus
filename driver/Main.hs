module Main where

import qualified Data.ByteString.Lazy.Char8 as BS
import Hibiscus.Lexer (runAlex)
import Hibiscus.Parser (parseHibiscus)
import Hibiscus.Type2 (typeInfer)
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
      case typeInfer parseResult of
        Right (_, decs) -> mapM_ print decs
        Left err -> print err

      -- case typeInfer parseResult of
      --   Left err -> putStrLn $ "Check Error: " ++ err
      --   Right (env, de) -> do
      --     print env
      --     mapM_ print de

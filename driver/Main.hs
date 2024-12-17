module Main where

import Control.Monad (when)
import qualified Data.ByteString.Lazy.Char8 as BS
import Hibiscus.CodeGen (defaultConfig, generate, instructionsToString)
import Hibiscus.Lexer (runAlex)
import Hibiscus.Parser (parseHibiscus)
import Hibiscus.Type2 (typeInfer)
import System.Environment (getArgs)

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
      -- print parseResult
      putStrLn "\n----- Type Check Result ---------------"
      case typeInfer parseResult of
        Left err -> putStrLn $ "Check Error: " ++ err
        Right (env, de) -> do
          -- print env
          -- mapM_ print de
          -- print de
          let code = generate defaultConfig de
          print de
          -- print env
          -- putStrLn (instructionsToString code)
          putStrLn $ show code
          writeFile (inputFilePath ++ ".asm") (instructionsToString code)

{-# LANGUAGE BangPatterns #-}

module TestEverything where

import System.Exit

import qualified Data.ByteString.Lazy.Char8 as BS
import Data.Either (either)
import Hibiscus.CodeGen (generate)
import Hibiscus.CodeGen.Constants (defaultConfig)
import Hibiscus.Parsing.Lexer (runAlex)
import Hibiscus.Parsing.Parser (parseHibiscus)
import Hibiscus.TypeInfer (infer)


testEverything :: FilePath -> IO ()
testEverything filepath = do
  content <- BS.readFile filepath
  !parseResult <- either (const $ die "Parse error") pure $ runAlex content parseHibiscus
  !inferResult <- either (const $ die "Infer error") pure $ infer parseResult
  let !asmResult = generate defaultConfig inferResult
  exitSuccess

{-# LANGUAGE BangPatterns #-}

module Main where

import TestEverything (testEverything)


main :: IO ()
main = testEverything "test/ifelse.hi"
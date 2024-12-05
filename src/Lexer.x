-- vim: set ft=haskell

{
-- At the top of the file, we define the module and its imports, similarly to Haskell.
module Lexer
  ( -- * Invoking Alex
    Alex
  , AlexPosn (..)
  , alexGetInput
  , alexError
  , runAlex
  , alexMonadScan

  , Range (..)
  , RangedToken (..)
  , Token (..)
  ) where

import Data.ByteString.Lazy.Char8 (ByteString)
import qualified Data.ByteString.Lazy.Char8 as BS
import Control.Monad (when)
}
-- In the middle, we insert our definitions for the lexer, which will generate the lexemes for our grammar.
%wrapper "monadUserState-bytestring"

$digit = [0-9]
$alpha = [a-zA-Z]

-- identifier regex
-- beginning with $alpha or _ and followed with other stuff
@id = ($alpha | \_) ($alpha | $digit | \_ | \' | \?)*

tokens :-

<0> $white+ ; -- ignore all white spaces

-- change to haskell-like comments
<0>       "--" .* ;
<0>       "{-"  { nestComment `andBegin` comment }
<0>       "-}"  { \_ _ -> alexError "error: unexpected closing comment" }
<comment> "{-"  { nestComment }
<comment> "-}"  { unnestComment }
<comment> .     ;
<comment> \n    ;

<0> let     { tok Let }
<0> in      { tok In }
<0> if      { tok If }
<0> then    { tok Then }
<0> else    { tok Else }

<0> "="     { tok Assign }
<0> ";"     { tok SemiColon }

<0> "+"     { tok Plus }
<0> "-"     { tok Minus }
<0> "*"     { tok Times }
<0> "/"     { tok Divide }

<0> "=="    { tok Eq }
<0> "<>"    { tok Neq }
<0> "<"     { tok Lt }
<0> "<="    { tok Le }
<0> ">"     { tok Gt }
<0> ">="    { tok Ge }

<0> "&"     { tok And }
<0> "|"     { tok Or }

<0> "("     { tok LPar }
<0> ")"     { tok RPar }

<0> "["     { tok LBrack }
<0> "]"     { tok RBrack }
<0> ","     { tok Comma }

<0> "::"    { tok DoubleColon }
<0> "->"    { tok Arrow }

<0> @id     { tokId }

<0> $digit+ { tokInt }
<0> $digit+\.$digit+ { tokFloat }
<0> \"[^\"]*\" { tokString }

{
-- At the bottom, we may insert more Haskell definitions, such as data structures, auxiliary functions, etc.
data AlexUserState = AlexUserState
  { nestLevel :: Int
  }

alexInitUserState :: AlexUserState
alexInitUserState = AlexUserState
  { nestLevel = 0
  }

get :: Alex AlexUserState
get = Alex $ \s -> Right (s, alex_ust s)

put :: AlexUserState -> Alex ()
put s' = Alex $ \s -> Right (s{alex_ust = s'}, ())

modify :: (AlexUserState -> AlexUserState) -> Alex ()
modify f = Alex $ \s -> Right (s{alex_ust = f (alex_ust s)}, ())

alexEOF :: Alex RangedToken
alexEOF = do
  startCode <- alexGetStartCode
  when (startCode == comment) $
    alexError "error: unclosed comment"
  (pos, _, _, _) <- alexGetInput
  pure $ RangedToken EOF (Range pos pos)

data Range = Range
  { start :: AlexPosn
  , stop :: AlexPosn
  } deriving (Eq, Show)

data RangedToken = RangedToken
  { rtToken :: Token
  , rtRange :: Range
  } deriving (Eq, Show)

data Token
  = Identifier ByteString
  -- const
  | String ByteString
  | Int Int
  | Float Float
  -- keyword
  | Let
  | In
  | If
  | Then
  | Else

  | Assign
  | SemiColon
  -- arith
  | Plus
  | Minus
  | Times
  | Divide
  -- comp
  | Eq
  | Neq
  | Lt
  | Le
  | Gt
  | Ge
  -- logic
  | And
  | Or
  -- paren
  | LPar
  | RPar
  -- list
  | Comma
  | LBrack
  | RBrack
  -- type
  | DoubleColon
  | Arrow
  -- eof
  | EOF
  deriving (Eq, Show)

mkRange :: AlexInput -> Int64 -> Range
mkRange (start, _, str, _) len = Range{start = start, stop = stop}
  where
    stop = BS.foldl' alexMove start $ BS.take len str

tokId :: AlexAction RangedToken
tokId inp@(_, _, str, _) len =
  pure RangedToken
    { rtToken = Identifier $ BS.take len str
    , rtRange = mkRange inp len
    }

tok :: Token -> AlexAction RangedToken
tok ctor inp len =
  pure RangedToken
  { rtToken = ctor
  , rtRange = mkRange inp len
  }

tokInt :: AlexAction RangedToken
tokInt inp@(_, _, str, _) len =
  pure RangedToken
    { rtToken = Int $ read $ BS.unpack $ BS.take len str
    , rtRange = mkRange inp len
    }

tokFloat :: AlexAction RangedToken
tokFloat inp@(_, _, str, _) len =
  pure RangedToken
    { rtToken = Float $ read $ BS.unpack $ BS.take len str
    , rtRange = mkRange inp len
    }

tokString :: AlexAction RangedToken
tokString inp@(_, _, str, _) len =
  pure RangedToken
    { rtToken = String $ BS.take len str
    , rtRange = mkRange inp len
    }

nestComment :: AlexAction RangedToken
nestComment input len = do
  modify $ \s -> s{nestLevel = nestLevel s + 1}
  skip input len

unnestComment :: AlexAction RangedToken
unnestComment input len = do
  state <- get
  let level = nestLevel state - 1
  put state{nestLevel = level}
  when (level == 0) $
    alexSetStartCode 0
  skip input len
}

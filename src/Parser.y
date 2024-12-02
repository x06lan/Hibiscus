-- vim: set ft=haskell
{
{-# LANGUAGE DeriveFoldable #-}
module Parser
  ( parseMiniML
  ) where

import Data.ByteString.Lazy.Char8 (ByteString)
import Data.Maybe (fromJust)
import Data.Monoid (First (..))

import qualified Lexer as L
import Ast
}

%name parseMiniML decs
%tokentype { L.RangedToken }
%error { parseError }
%monad { L.Alex } { >>= } { pure }
%lexer { lexer } { L.RangedToken L.EOF _ }

%token
  identifier  { L.RangedToken (L.Identifier _) _ }
  string      { L.RangedToken (L.String _) _ }
  integer     { L.RangedToken (L.Integer _) _ }
  let         { L.RangedToken L.Let _ }
  in          { L.RangedToken L.In _ }
  if          { L.RangedToken L.If _ }
  then        { L.RangedToken L.Then _ }
  else        { L.RangedToken L.Else _ }
  '+'         { L.RangedToken L.Plus _ }
  '-'         { L.RangedToken L.Minus _ }
  '*'         { L.RangedToken L.Times _ }
  '/'         { L.RangedToken L.Divide _ }
  '='         { L.RangedToken L.Eq _ }
  '<>'        { L.RangedToken L.Neq _ }
  '<'         { L.RangedToken L.Lt _ }
  '<='        { L.RangedToken L.Le _ }
  '>'         { L.RangedToken L.Gt _ }
  '>='        { L.RangedToken L.Ge _ }
  '&'         { L.RangedToken L.And _ }
  '|'         { L.RangedToken L.Or _ }
  '('         { L.RangedToken L.LPar _ }
  ')'         { L.RangedToken L.RPar _ }
  '['         { L.RangedToken L.LBrack _ }
  ']'         { L.RangedToken L.RBrack _ }
  ','         { L.RangedToken L.Comma _ }
  ':'         { L.RangedToken L.Colon _ }
  '->'        { L.RangedToken L.Arrow _ }

%right '->'
%left '|'
%left '&'
%nonassoc '=' '<>' '<' '>' '<=' '>='
%left '+' '-'
%left '*' '/'

%%

optional(p)
  :   { Nothing }
  | p { Just $1 }

many_rev(p)
  :               { [] }
  | many_rev(p) p { $2 : $1 }

many(p)
  : many_rev(p) { reverse $1 }

name :: { Name L.Range }
  : identifier { unTok $1 (\range (L.Identifier name) -> Name range name) }

type :: { Type L.Range }
  : name            { TVar (info $1) $1 }
  | '(' ')'         { TUnit (L.rtRange $1 <-> L.rtRange $2) }
  | '[' type ']'    { TList (L.rtRange $1 <-> L.rtRange $3) $2 }
  | type '->' type  { TArrow (info $1 <-> info $3) $1 $3 }

typeAnnotation :: { Type L.Range }
  : ':' type { $2 }

argument :: { Argument L.Range }
  : name { Argument (info $1) $1 Nothing }

dec
  : let name many(argument) optional(typeAnnotation) '=' expr { Dec (L.rtRange $1 <-> info $6) $2 $3 $4 $6 }

decs
  : many(dec) { $1 }

expr :: { Expr L.Range }
  : integer   { unTok $1 (\range (L.Integer int) -> EInt range int) }
  | name      { EVar (info $1) $1 }
  | string    { unTok $1 (\range (L.String string) -> EString range string) }

{
parseError :: L.RangedToken -> L.Alex a
parseError _ = do
  (L.AlexPn _ line column, _, _, _) <- L.alexGetInput
  L.alexError $ "Parse error at line " <> show line <> ", column " <> show column

lexer :: (L.RangedToken -> L.Alex a) -> L.Alex a
lexer = (=<< L.alexMonadScan)

unTok :: L.RangedToken -> (L.Range -> L.Token -> a) -> a
unTok (L.RangedToken tok range) ctor = ctor range tok

info :: Foldable f => f a -> a
info = fromJust . getFirst . foldMap pure

-- join two ranges
(<->) :: L.Range -> L.Range -> L.Range
L.Range a1 _ <-> L.Range _ b2 = L.Range a1 b2
}

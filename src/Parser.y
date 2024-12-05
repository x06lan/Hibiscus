-- vim: set ft=haskell
{
{-# LANGUAGE DeriveFoldable #-}
module Parser
  ( parseHibiscus
  ) where

import Data.ByteString.Lazy.Char8 (ByteString)
import Data.Maybe (fromJust)
import Data.Monoid (First (..))

import qualified Lexer as L
import Ast
}

%name parseHibiscus decs
%tokentype { L.RangedToken }
%error { parseError }
%monad { L.Alex } { >>= } { pure }
%lexer { lexer } { L.RangedToken L.EOF _ }
%expect 0

%token
  identifier  { L.RangedToken (L.Identifier _) _ }
  string      { L.RangedToken (L.String _) _ }
  int         { L.RangedToken (L.Int _) _ }
  float       { L.RangedToken (L.Float _) _ }
  let         { L.RangedToken L.Let _ }
  in          { L.RangedToken L.In _ }
  if          { L.RangedToken L.If _ }
  then        { L.RangedToken L.Then _ }
  else        { L.RangedToken L.Else _ }
  '='         { L.RangedToken L.Assign _ }
  ';'         { L.RangedToken L.SemiColon _ }
  '+'         { L.RangedToken L.Plus _ }
  '-'         { L.RangedToken L.Minus _ }
  '*'         { L.RangedToken L.Times _ }
  '/'         { L.RangedToken L.Divide _ }
  '=='        { L.RangedToken L.Eq _ }
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
  '::'        { L.RangedToken L.DoubleColon _ }
  '->'        { L.RangedToken L.Arrow _ }

%right else in
%right '->'
%left '|'
%left '&'
%nonassoc '==' '<>' '<' '>' '<=' '>='
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

sepBy_rev(p, sep)
  :                         { [] }
  | sepBy_rev(p, sep) sep p { $3 : $1 }

sepBy(p, sep)
  : sepBy_rev(p, sep){ reverse $1 }

name :: { Name L.Range }
  : identifier { unTok $1 (\range (L.Identifier name) -> Name range name) }

type :: { Type L.Range }
  : name            { TVar (info $1) $1 }
  | '(' ')'         { TUnit (L.rtRange $1 <-> L.rtRange $2) }
  | '(' type ')'    { TPar (L.rtRange $1 <-> L.rtRange $3) $2 }
  | '[' type ']'    { TList (L.rtRange $1 <-> L.rtRange $3) $2 }
  | type '->' type  { TArrow (info $1 <-> info $3) $1 $3 }

argument :: { Argument L.Range }
  : name { Argument (info $1) $1 }

dec :: { Dec L.Range }
  : name many(argument) '=' expr ';'  { Dec (info $1 <-> info $4) $1 $2 $4 }
  | name '::' type                { DecAnno (info $1 <-> info $3) $1 $3 }

decs :: { [Dec L.Range] }
  : many(dec) { $1 }

expr :: { Expr L.Range }
  : exprapp             { $1 }
  | exprcond            { $1 }
  | '-' expr            { ENeg (L.rtRange $1 <-> info $2) $2 }
  -- Arithmetic operators
  | expr '+'  expr      { EBinOp (info $1 <-> info $3) $1 (Plus (L.rtRange $2)) $3 }
  | expr '-'  expr      { EBinOp (info $1 <-> info $3) $1 (Minus (L.rtRange $2)) $3 }
  | expr '*'  expr      { EBinOp (info $1 <-> info $3) $1 (Times (L.rtRange $2)) $3 }
  | expr '/'  expr      { EBinOp (info $1 <-> info $3) $1 (Divide (L.rtRange $2)) $3 }
  -- Comparison operators
  | expr '==' expr      { EBinOp (info $1 <-> info $3) $1 (Eq (L.rtRange $2)) $3 }
  | expr '<>' expr      { EBinOp (info $1 <-> info $3) $1 (Neq (L.rtRange $2)) $3 }
  | expr '<'  expr      { EBinOp (info $1 <-> info $3) $1 (Lt (L.rtRange $2)) $3 }
  | expr '<=' expr      { EBinOp (info $1 <-> info $3) $1 (Le (L.rtRange $2)) $3 }
  | expr '>'  expr      { EBinOp (info $1 <-> info $3) $1 (Gt (L.rtRange $2)) $3 }
  | expr '>=' expr      { EBinOp (info $1 <-> info $3) $1 (Ge (L.rtRange $2)) $3 }
  -- Logical operators
  | expr '&'  expr      { EBinOp (info $1 <-> info $3) $1 (And (L.rtRange $2)) $3 }
  | expr '|'  expr      { EBinOp (info $1 <-> info $3) $1 (Or (L.rtRange $2)) $3 }
  | let decs in expr    { ELetIn (L.rtRange $1 <-> info $4) $2 $4 }

exprapp :: { Expr L.Range }
  : exprapp atom  { EApp (info $1 <-> info $2) $1 $2 }
  | atom          { $1 }

exprcond :: { Expr L.Range }
  : if expr then expr else expr { EIfThenElse (L.rtRange $1 <-> info $6) $2 $4 $6 }

atom :: { Expr L.Range }
  : int                       { unTok $1 (\range (L.Int int) -> EInt range int) }
  | float                     { unTok $1 (\range (L.Float float) -> EFloat range float) }
  | name                      { EVar (info $1) $1 }
  | string                    { unTok $1 (\range (L.String string) -> EString range string) }
  | '(' ')'                   { EUnit (L.rtRange $1 <-> L.rtRange $2) }
  | '[' sepBy(expr, ',') ']'  { EList (L.rtRange $1 <-> L.rtRange $3) $2 }
  | '(' expr ')'              { EPar (L.rtRange $1 <-> L.rtRange $3) $2 }

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

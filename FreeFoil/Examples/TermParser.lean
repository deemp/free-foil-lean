import Std.Internal.Parsec.String

namespace FreeFoil.Examples.TermParser

open Std.Internal.Parsec
open Std.Internal.Parsec.String (Parser skipString ws)

private partial def skipBlockComment : Parser Unit :=
  skipString "-}" <|> (any *> skipBlockComment)

def trivia : Parser Unit := do
  ws
  let _ ← many do
    (skipString "--" *> many (satisfy (· != '\n')) *> pure ()) <|>
      (skipString "{-" *> skipBlockComment)
    ws

def symbol (text : String) : Parser Unit :=
  skipString text *> trivia

private def isLetter (c : Char) : Bool :=
  c.isAlpha || (c >= 'À' && c <= 'ÿ' && c != '×' && c != '÷')

private def isIdentRest (c : Char) : Bool :=
  isLetter c || c.isDigit || c == '_' || c == '\''

def identifier (reserved : List String) : Parser String := do
  let name ← attempt do
    let first ← satisfy isLetter
    let rest ← many (satisfy isIdentRest)
    let name := String.ofList (first :: rest.toList)
    if reserved.contains name then fail "expected an identifier"
    else pure name
  trivia
  pure name

def keyword (text : String) : Parser Unit :=
  attempt (skipString text *> notFollowedBy (satisfy isIdentRest)) *> trivia

def parenthesized (inner : Parser α) : Parser α :=
  symbol "(" *> inner <* symbol ")"

def applications (app : α → α → α) (atom : Parser α) : Parser α := do
  let fn ← atom
  let args ← many atom
  pure (args.foldl app fn)

end FreeFoil.Examples.TermParser

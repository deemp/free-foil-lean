import FreeFoil.Examples.LambdaPi
import Std.Internal.Parsec.String

namespace FreeFoil.Examples.LambdaPi

inductive Command where
  | compute (term type : Raw)
  | check (term type : Raw)

namespace Parser

open Std.Internal.Parsec
open Std.Internal.Parsec.String (Parser skipString ws)

private partial def skipBlockComment : Parser Unit :=
  skipString "-}" <|> (any *> skipBlockComment)

private def trivia : Parser Unit := do
  ws
  let _ ← many do
    (skipString "--" *> many (satisfy (· != '\n')) *> pure ()) <|>
      (skipString "{-" *> skipBlockComment)
    ws

private def symbol (text : String) : Parser Unit :=
  skipString text *> trivia

private def isLetter (c : Char) : Bool :=
  c.isAlpha || (c >= 'À' && c <= 'ÿ' && c != '×' && c != '÷')

private def isIdentRest (c : Char) : Bool :=
  isLetter c || c.isDigit || c == '_' || c == '\''

private def identifier : Parser String := do
  let name ← attempt do
    let first ← satisfy isLetter
    let rest ← many (satisfy isIdentRest)
    let name := String.ofList (first :: rest.toList)
    if name == "compute" || name == "check" then fail "expected an identifier"
    else pure name
  trivia
  pure name

private def keyword (text : String) : Parser Unit :=
  attempt (skipString text *> notFollowedBy (satisfy isIdentRest)) *> trivia

private partial def pattern : Parser (Binder sig String) :=
  (symbol "_" *> pure Raw.wildcard) <|> (Raw.varPattern <$> identifier) <|> do
    symbol "("
    let left ← pattern
    symbol ","
    let right ← pattern
    symbol ")"
    pure (Raw.pairPattern left right)

private partial def term : Parser Raw :=
  lambda <|> pi <|> projection "π₁" Raw.first <|> projection "π₂" Raw.second <|>
    (symbol "𝕌" *> pure Raw.univ) <|> applicationOrProduct
where
  lambda : Parser Raw := do
    symbol "λ"
    let binder ← pattern
    symbol "."
    pure (Raw.lamPattern binder (← term))
  pi : Parser Raw := do
    symbol "Π"
    symbol "("
    let binder ← pattern
    symbol ":"
    let domain ← term
    symbol ")"
    symbol "→"
    pure (Raw.piPattern binder domain (← term))
  projection (name : String) (op : Raw → Raw) : Parser Raw := do
    symbol name
    symbol "("
    let arg ← term
    symbol ")"
    pure (op arg)
  operand : Parser Raw :=
    (Raw.var <$> identifier) <|> do
      symbol "("
      let inner ← term
      symbol ")"
      pure inner
  application (fn : Raw) : Parser Raw := do
    let args ← many operand
    pure (args.foldl Raw.app fn)
  finishApplicationOrProduct (fn : Raw) : Parser Raw := do
    let left ← application fn
    if let some _ ← optional (symbol "×") then
      pure (Raw.product left (← application (← operand)))
    else
      pure left
  applicationOrProduct : Parser Raw :=
    (identifier >>= (finishApplicationOrProduct ∘ Raw.var)) <|> do
      symbol "("
      let left ← term
      if let some _ ← optional (symbol ",") then
        let right ← term
        symbol ")"
        pure (Raw.pair left right)
      else
        symbol ")"
        finishApplicationOrProduct left

private def command : Parser Command := do
  let make ← (keyword "compute" *> pure Command.compute) <|>
    (keyword "check" *> pure Command.check)
  let value ← term
  symbol ":"
  let type ← term
  let _ ← optional (symbol ";")
  pure (make value type)

def parseTerm (input : String) : Except String Raw :=
  (trivia *> term <* eof).run input

def parseProgram (input : String) : Except String (Array Command) :=
  (trivia *> many command <* eof).run input

end Parser

private def renderPattern (shape : Pattern) (names : List String) : String × List String :=
  match shape, names with
  | .wildcard, _ => ("_", names)
  | .variable, name :: rest => (name, rest)
  | .variable, [] => ("_", [])
  | .pair left right, _ =>
    let (fst, rest) := renderPattern left names
    let (snd, rest) := renderPattern right rest
    (s!"({fst}, {snd})", rest)

private def renderTerm (prec : Nat) (value : Raw) : String :=
  let paren (own : Nat) (text : String) := if prec > own then s!"({text})" else text
  match value with
  | .var name => name
  | .node op terms binders bodies =>
    match op with
    | .app => paren 1 s!"{renderTerm 1 (terms 0)} {renderTerm 2 (terms 1)}"
    | .lam =>
      let binder := binders 0
      let pat := (renderPattern binder.shape binder.names).1
      paren 0 s!"λ {pat}. {renderTerm 0 (bodies 0)}"
    | .pi =>
      let binder := binders 0
      let pat := (renderPattern binder.shape binder.names).1
      paren 0 s!"Π ({pat} : {renderTerm 0 (terms 0)}) → {renderTerm 0 (bodies 0)}"
    | .univ => paren 0 "𝕌"
    | .pair => paren 0 s!"({renderTerm 0 (terms 0)}, {renderTerm 0 (terms 1)})"
    | .first => paren 0 s!"π₁({renderTerm 0 (terms 0)})"
    | .second => paren 0 s!"π₂({renderTerm 0 (terms 0)})"
    | .product => paren 0 s!"{renderTerm 1 (terms 0)} × {renderTerm 1 (terms 1)}"
termination_by structural value

def prettyTerm (value : Raw) : String := renderTerm 0 value

inductive InterpretError where
  | scope (error : ResolveError String)
  | evaluation (error : EvalError)
  deriving Repr

instance : ToString InterpretError where
  toString
    | .scope (.unbound name) => s!"unbound name '{name}'"
    | .scope (.duplicateBinder names) => s!"duplicate name in binder pattern ({String.intercalate ", " names})"
    | .evaluation .outOfFuel => "evaluation ran out of fuel"

/-- Evaluate the term in a compute command. Type annotations and check commands are
parsed so the interpreter can read upstream programs. -/
def interpret (fuel : Nat) (command : Command) : Except InterpretError String := do
  match command with
  | .check _ _ => pure "check is not yet implemented"
  | .compute value _ =>
    let term ← (AST.fromClosed value).mapError .scope
    let result ← (whnf [] fuel term).mapError .evaluation
    pure (prettyTerm (result.toNamed [] fun x => nomatch x.property))

end FreeFoil.Examples.LambdaPi

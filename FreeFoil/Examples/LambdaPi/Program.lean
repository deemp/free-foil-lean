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

private partial def term : Parser NamedTerm :=
  lambda <|> pi <|> projection "π₁" NamedTerm.first <|> projection "π₂" NamedTerm.second <|>
    (symbol "𝕌" *> pure NamedTerm.univ) <|> applicationOrProduct
where
  lambda : Parser NamedTerm := do
    symbol "λ"
    let binder ← pattern
    symbol "."
    pure (.lam (BoundSyntax.ofBinder binder (← term)))
  pi : Parser NamedTerm := do
    symbol "Π"
    symbol "("
    let binder ← pattern
    symbol ":"
    let domain ← term
    symbol ")"
    symbol "→"
    pure (.pi domain (BoundSyntax.ofBinder binder (← term)))
  projection (name : String) (op : NamedTerm → NamedTerm) : Parser NamedTerm := do
    symbol name
    symbol "("
    let arg ← term
    symbol ")"
    pure (op arg)
  operand : Parser NamedTerm :=
    (NamedTerm.var <$> identifier) <|> do
      symbol "("
      let inner ← term
      symbol ")"
      pure inner
  application (fn : NamedTerm) : Parser NamedTerm := do
    let args ← many operand
    pure (args.foldl NamedTerm.app fn)
  finishApplicationOrProduct (fn : NamedTerm) : Parser NamedTerm := do
    let left ← application fn
    if let some _ ← optional (symbol "×") then
      pure (.product left (← application (← operand)))
    else
      pure left
  applicationOrProduct : Parser NamedTerm :=
    (identifier >>= (finishApplicationOrProduct ∘ NamedTerm.var)) <|> do
      symbol "("
      let left ← term
      if let some _ ← optional (symbol ",") then
        let right ← term
        symbol ")"
        pure (.pair left right)
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
  pure (make value.toRaw type.toRaw)

def parseTerm (input : String) : Except String Raw :=
  (trivia *> (NamedTerm.toRaw <$> term) <* eof).run input

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

private def renderTerm (prec : Nat) (value : NamedTerm) : String :=
  let paren (own : Nat) (text : String) := if prec > own then s!"({text})" else text
  match value with
  | .var name => name
  | .app fn arg => paren 1 s!"{renderTerm 1 fn} {renderTerm 2 arg}"
  | .lam ⟨shape, names, _, body⟩ =>
    let pat := (renderPattern shape names).1
    paren 0 s!"λ {pat}. {renderTerm 0 body}"
  | .pi domain ⟨shape, names, _, codomain⟩ =>
    let pat := (renderPattern shape names).1
    paren 0 s!"Π ({pat} : {renderTerm 0 domain}) → {renderTerm 0 codomain}"
  | .univ => paren 0 "𝕌"
  | .pair fst snd => paren 0 s!"({renderTerm 0 fst}, {renderTerm 0 snd})"
  | .first term => paren 0 s!"π₁({renderTerm 0 term})"
  | .second term => paren 0 s!"π₂({renderTerm 0 term})"
  | .product fst snd => paren 0 s!"{renderTerm 1 fst} × {renderTerm 1 snd}"
termination_by structural value

def prettyTerm (value : Raw) : String := renderTerm 0 (NamedTerm.fromRaw value)

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
    pure (renderTerm 0 (Term.toNamedTerm [] result fun x => nomatch x.property))

end FreeFoil.Examples.LambdaPi

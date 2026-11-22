import FreeFoil.Examples.LambdaPi.NbE
import FreeFoil.Examples.LambdaPi.Program
import FreeFoil.Examples.NbEDemos.Booleans
import FreeFoil.Examples.NbEDemos.LambdaLet
import FreeFoil.Examples.NbEDemos.Pairs
import FreeFoil.Examples.NbEDemos.Naturals
import FreeFoil.Examples.NbEDemos.Fragments

namespace FreeFoil.Examples.NbEDemos

open Std.Internal.Parsec
open Std.Internal.Parsec.String (Parser)
open TermParser

/-- A named context for parsing and rendering open terms. -/
structure OpenNames where
  names : List String
  distinct : names.Nodup

def OpenNames.ofList (names : List String) : Except String OpenNames :=
  if distinct : names.Nodup then pure ⟨names, distinct⟩
  else throw "free variable names must be distinct"

def OpenNames.scope (context : OpenNames) : Scope :=
  List.range context.names.length

def OpenNames.resolve (context : OpenNames) (term : Syntax sig String) :
    Except (ResolveError String) (AST sig context.scope) :=
  AST.fromNamed context.scope (fun name =>
    if mem : name ∈ context.names then
      some ⟨context.names.idxOf name, List.mem_range.mpr (List.idxOf_lt_length_of_mem mem)⟩
    else none) term

def OpenNames.label (context : OpenNames) (name : Name context.scope) : String :=
  context.names[name.id]'(List.mem_range.mp name.property)

structure Demo (sig : Signature) where
  parse : String → Except String (Syntax sig String)
  pretty : Syntax sig String → String
  rules : NbE.Rules sig NbE.NoContext

private def resolveMessage : ResolveError String → String
  | .unbound name => s!"unbound name '{name}'"
  | .duplicateBinder names => s!"duplicate names in binder ({String.intercalate ", " names})"

def Demo.normalize (demo : Demo sig) (fuel : Nat) (source : String)
    (freeNames : List String := []) : Except String String := do
  let context ← OpenNames.ofList freeNames
  let raw ← demo.parse source
  let term ← (context.resolve raw).mapError resolveMessage
  let result ← (NbE.nf demo.rules fuel () term).mapError fun
    | .outOfFuel => "evaluation ran out of fuel"
    | .invalidBinder expected actual => s!"expected a pattern binding {expected} names, got {actual}"
  pure (demo.pretty (result.toNamed context.scope context.label))

private def parseTerm (parser : Parser α) (source : String) : Except String α :=
  (trivia *> parser <* eof).run source

private partial def lambdaPiTerm : Parser LambdaPi.NamedTerm :=
  lambda <|> pi <|> applications .app atom
where
  lambda : Parser LambdaPi.NamedTerm := do
    symbol "\\"
    let name ← identifier []
    symbol "."
    pure (.lam (BoundSyntax.ofBinder (LambdaPi.Raw.varPattern name) (← lambdaPiTerm)))
  pi : Parser LambdaPi.NamedTerm := do
    let (name, domain) ← attempt do
      let binder ← parenthesized do
        let name ← identifier []
        symbol ":"
        pure (name, ← lambdaPiTerm)
      symbol "->"
      pure binder
    pure (.pi domain (BoundSyntax.ofBinder (LambdaPi.Raw.varPattern name) (← lambdaPiTerm)))
  atom : Parser LambdaPi.NamedTerm :=
    (.var <$> identifier []) <|> parenthesized lambdaPiTerm

def lambdaPi : Demo LambdaPi.sig where
  parse := parseTerm (LambdaPi.NamedTerm.toRaw <$> lambdaPiTerm)
  pretty := LambdaPi.prettyNbETerm
  rules := LambdaPi.nbeRules

private partial def booleanTerm : Parser Booleans.NamedTerm :=
  (keyword "true" *> pure .trueVal) <|>
  (keyword "false" *> pure .falseVal) <|>
  (.var <$> identifier ["true", "false", "if", "then", "else"]) <|>
  parenthesized booleanTerm <|> do
    keyword "if"
    let condition ← booleanTerm
    keyword "then"
    let thenBranch ← booleanTerm
    keyword "else"
    pure (.cond condition thenBranch (← booleanTerm))

private def renderBoolean : Booleans.NamedTerm → String
  | .var name => name
  | .trueVal => "true"
  | .falseVal => "false"
  | .cond cond yes no => s!"if {renderBoolean cond} then {renderBoolean yes} else {renderBoolean no}"

def booleans : Demo Booleans.sig where
  parse := parseTerm (Booleans.NamedTerm.toRaw <$> booleanTerm)
  pretty := renderBoolean ∘ Booleans.NamedTerm.fromRaw
  rules := Booleans.nbeRules

private partial def letTerm : Parser LambdaLet.NamedTerm :=
  lambda <|> binding <|> applications .app atom
where
  name : Parser String := identifier ["let", "in"]
  lambda : Parser LambdaLet.NamedTerm := do
    symbol "\\"
    let binder ← name
    symbol "."
    pure (.lam ⟨(), [binder], rfl, ← letTerm⟩)
  binding : Parser LambdaLet.NamedTerm := do
    keyword "let"
    let binder ← name
    symbol "="
    let value ← letTerm
    keyword "in"
    pure (.letIn value ⟨(), [binder], rfl, ← letTerm⟩)
  atom : Parser LambdaLet.NamedTerm :=
    (.var <$> name) <|> parenthesized letTerm

private def wrap (keep : Bool) (text : String) : String :=
  if keep then s!"({text})" else text

private def renderLet (prec : Nat) (term : LambdaLet.NamedTerm) : String :=
  match term with
  | .var name => name
  | .app fn arg => wrap (prec > 1) s!"{renderLet 1 fn} {renderLet 2 arg}"
  | .lam ⟨(), names, arity, body⟩ =>
    let name := names[0]'(by simp [arity, LambdaLet.arity])
    wrap (prec > 0) s!"\\{name}. {renderLet 0 body}"
  | .letIn value ⟨(), names, arity, body⟩ =>
    let name := names[0]'(by simp [arity, LambdaLet.arity])
    wrap (prec > 0) s!"let {name} = {renderLet 0 value} in {renderLet 0 body}"
termination_by structural term

def lambdaLet : Demo LambdaLet.sig where
  parse := parseTerm (LambdaLet.NamedTerm.toRaw <$> letTerm)
  pretty := renderLet 0 ∘ LambdaLet.NamedTerm.fromRaw
  rules := LambdaLet.nbeRules

private partial def pairsTerm : Parser Pairs.NamedTerm :=
  (keyword "fst" *> (.first <$> atom)) <|>
  (keyword "snd" *> (.second <$> atom)) <|>
  split <|> atom
where
  name : Parser String := identifier ["fst", "snd", "split", "as", "in"]
  split : Parser Pairs.NamedTerm := do
    keyword "split"
    let pair ← pairsTerm
    keyword "as"
    let (first, second) ← parenthesized do
      let first ← name
      symbol ","
      pure (first, ← name)
    keyword "in"
    pure (.split pair ⟨(), [first, second], rfl, ← pairsTerm⟩)
  atom : Parser Pairs.NamedTerm :=
    (.var <$> name) <|> parenthesized do
      let first ← pairsTerm
      if (← optional (symbol ",")).isSome then
        pure (.pair first (← pairsTerm))
      else pure first

private def renderPairs (operand : Bool) (term : Pairs.NamedTerm) : String :=
  match term with
  | .var name => name
  | .pair first second => s!"({renderPairs false first}, {renderPairs false second})"
  | .first pair => wrap operand s!"fst {renderPairs true pair}"
  | .second pair => wrap operand s!"snd {renderPairs true pair}"
  | .split pair ⟨(), names, arity, body⟩ =>
    let first := names[0]'(by simp [arity, Pairs.arity])
    let second := names[1]'(by simp [arity, Pairs.arity])
    wrap operand s!"split {renderPairs false pair} as ({first}, {second}) in {renderPairs false body}"
termination_by structural term

def pairs : Demo Pairs.sig where
  parse := parseTerm (Pairs.NamedTerm.toRaw <$> pairsTerm)
  pretty := renderPairs false ∘ Pairs.NamedTerm.fromRaw
  rules := Pairs.nbeRules

private partial def naturalsTerm : Parser Naturals.NamedTerm :=
  (keyword "suc" *> (.suc <$> atom)) <|> recursion <|> atom
where
  name : Parser String := identifier ["zero", "suc", "natrec"]
  atom : Parser Naturals.NamedTerm :=
    (keyword "zero" *> pure .zero) <|> (.var <$> name) <|> parenthesized naturalsTerm
  recursion : Parser Naturals.NamedTerm := do
    keyword "natrec"
    let scrutinee ← naturalsTerm
    symbol "{"
    keyword "zero"
    symbol "->"
    let base ← naturalsTerm
    symbol ";"
    keyword "suc"
    let pred ← name
    symbol ","
    let previous ← name
    symbol "->"
    let step ← naturalsTerm
    symbol "}"
    pure (.natrec scrutinee base ⟨(), [pred, previous], rfl, step⟩)

private def renderNaturals (operand : Bool) (term : Naturals.NamedTerm) : String :=
  match term with
  | .var name => name
  | .zero => "zero"
  | .suc pred => wrap operand s!"suc {renderNaturals true pred}"
  | .natrec scrutinee base ⟨(), names, arity, step⟩ =>
    let pred := names[0]'(by simp [arity, Naturals.arity])
    let previous := names[1]'(by simp [arity, Naturals.arity])
    let baseBranch := s!"zero -> {renderNaturals false base}"
    let stepBranch := s!"suc {pred}, {previous} -> {renderNaturals false step}"
    wrap operand s!"natrec {renderNaturals false scrutinee} \{ {baseBranch}; {stepBranch} }"
termination_by structural term

def naturals : Demo Naturals.sig where
  parse := parseTerm (Naturals.NamedTerm.toRaw <$> naturalsTerm)
  pretty := renderNaturals false ∘ Naturals.NamedTerm.fromRaw
  rules := Naturals.nbeRules

def fragments : Demo Fragments.sig where
  parse := Fragments.parse
  pretty := Fragments.pretty
  rules := Fragments.nbeRules

def monolith : Demo Monolith.sig where
  parse := Monolith.parse
  pretty := Monolith.pretty
  rules := Monolith.nbeRules

end FreeFoil.Examples.NbEDemos

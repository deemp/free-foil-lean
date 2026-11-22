import FreeFoil
import FreeFoil.Derive
import FreeFoil.Examples.TermParser

namespace FreeFoil.Examples.NbEDemos.Monolith

inductive Pattern where
  | single
  | pair
  deriving DecidableEq

def Pattern.binders : Pattern → Nat
  | .single => 1
  | .pair => 2

inductive NamedTerm where
  | var (name : String)
  | lam (body : BoundSyntax Pattern Pattern.binders NamedTerm)
  | app (fn arg : NamedTerm)
  | pi (domain : NamedTerm) (codomain : BoundSyntax Pattern Pattern.binders NamedTerm)
  | pair (first second : NamedTerm)
  | first (pair : NamedTerm)
  | second (pair : NamedTerm)
  | split (pair : NamedTerm) (body : BoundSyntax Pattern Pattern.binders NamedTerm)
  | zero
  | suc (pred : NamedTerm)
  | natrec (scrutinee base : NamedTerm) (step : BoundSyntax Pattern Pattern.binders NamedTerm)

derive_free_foil NamedTerm with Pattern, Pattern.binders

open Std.Internal.Parsec
open Std.Internal.Parsec.String (Parser)
open TermParser

private def identifier : Parser String :=
  TermParser.identifier ["fst", "snd", "split", "as", "in", "zero", "suc", "natrec"]

private def pattern : Parser (Binder sig String) :=
  (fun name => ⟨.single, [name], rfl⟩) <$> identifier <|> parenthesized (do
    let first ← identifier
    symbol ","
    let second ← identifier
    pure ⟨.pair, [first, second], rfl⟩)

private partial def term : Parser NamedTerm :=
  lambda <|> pi <|> split <|> natrec <|> application
where
  lambda := do
    symbol "\\"
    let binder ← pattern
    symbol "."
    pure (.lam (BoundSyntax.ofBinder binder (← term)))
  pi := do
    let (binder, domain) ← attempt do
      let declaration ← parenthesized do
        let binder ← pattern
        symbol ":"
        pure (binder, ← term)
      symbol "->"
      pure declaration
    pure (.pi domain (BoundSyntax.ofBinder binder (← term)))
  split := do
    keyword "split"
    let pair ← term
    keyword "as"
    let binder ← pattern
    keyword "in"
    pure (.split pair (BoundSyntax.ofBinder binder (← term)))
  natrec := do
    keyword "natrec"
    let scrutinee ← term
    symbol "{"
    keyword "zero"
    symbol "->"
    let base ← term
    symbol ";"
    keyword "suc"
    let binder ← pattern
    symbol "->"
    let step ← term
    symbol "}"
    pure (.natrec scrutinee base (BoundSyntax.ofBinder binder step))
  atom :=
    (keyword "zero" *> pure .zero) <|> (.var <$> identifier) <|>
    parenthesized (do
      let first ← term
      if (← optional (symbol ",")).isSome then
        return .pair first (← term)
      else
        return first)
  application := do
    let head ← (keyword "fst" *> (.first <$> atom)) <|> (keyword "snd" *> (.second <$> atom)) <|>
      (keyword "suc" *> (.suc <$> atom)) <|> atom
    let args ← many atom
    pure (args.foldl .app head)

/-- Parse the concrete syntax shared by the two mixed language implementations. -/
def parse (source : String) : Except String Raw :=
  (trivia *> (NamedTerm.toRaw <$> term) <* eof).run source

private def renderPattern (shape : Pattern) (names : List String) : String :=
  match shape with
  | .single => names.headD ""
  | .pair => s!"({String.intercalate ", " names})"

private def render (prec : Nat) (term : NamedTerm) : String :=
  let wrap own text := if prec > own then s!"({text})" else text
  match term with
  | .var name => name
  | .lam ⟨shape, names, _, body⟩ =>
    wrap 0 s!"\\{renderPattern shape names}. {render 0 body}"
  | .app fn arg => wrap 1 s!"{render 1 fn} {render 2 arg}"
  | .pi domain ⟨shape, names, _, body⟩ =>
    wrap 0 s!"({renderPattern shape names} : {render 0 domain}) -> {render 0 body}"
  | .pair first second => s!"({render 0 first}, {render 0 second})"
  | .first pair => wrap 1 s!"fst {render 2 pair}"
  | .second pair => wrap 1 s!"snd {render 2 pair}"
  | .split pair ⟨shape, names, _, body⟩ =>
    wrap 0 s!"split {render 0 pair} as {renderPattern shape names} in {render 0 body}"
  | .zero => "zero"
  | .suc pred => wrap 1 s!"suc {render 2 pred}"
  | .natrec scrutinee base ⟨shape, names, _, step⟩ =>
    wrap 0 s!"natrec {render 0 scrutinee} \{ zero -> {render 0 base}; suc {renderPattern shape names} -> {render 0 step} }"
termination_by structural term

def pretty : Raw → String := render 0 ∘ NamedTerm.fromRaw

private def project (evaluator : NbE.Evaluator sig scope) (index : Fin 2) :
    NbE.Value sig scope → NbE.Result (Option (NbE.Value sig scope))
  | .node .pair terms _ => some <$> evaluator.force (terms index)
  | _ => pure none

/-- Independent dispatch for the flat-signature reference and benchmark. -/
def nbeRules : NbE.Rules sig NbE.NoContext where
  reduce evaluator _ op terms children :=
    match op with
    | .app => evaluator.eliminate .app terms children 0 fun
      | .node .lam _ lambda =>
        some <$> evaluator.instantiateAtArity (lambda 0) (fun _ : Fin 1 => terms 1)
      | _ => pure none
    | .first => evaluator.eliminate .first terms children 0 (project evaluator 0)
    | .second => evaluator.eliminate .second terms children 0 (project evaluator 1)
    | .split => evaluator.eliminate .split terms children 0 fun
      | .node .pair fields _ => some <$> evaluator.instantiateAtArity (children 0) fields
      | _ => pure none
    | .natrec => evaluator.eliminate .natrec terms children 0 fun
      | .node .zero _ _ => some <$> evaluator.force (terms 1)
      | .node .suc args _ =>
        let pred := args 0
        let recursive : NbE.Thunk sig _ := .node .natrec (Fin.cases pred fun _ => terms 1) children
        some <$> evaluator.instantiateAtArity (children 0) (Fin.cases pred fun _ : Fin 1 => recursive)
      | _ => pure none
    | _ => pure none
  extend _ _ _ _ _ _ := pure ()
  isHead op i := match op with
    | .app | .natrec => i == 0
    | .first | .second | .split => true
    | _ => false
  eta op := match op with
    | .lam => some {
      term i _ _ := Fin.elim0 i
      body {scope} _ binder _ value := do
        if arity : binder.names.length = 1 then
          have bound : 0 < binder.names.length := by rw [arity]; decide
          let name : Name (binder.names ++ scope) :=
            ⟨binder.names[0], List.mem_append_left _ (List.getElem_mem bound)⟩
          some (.node .app (Fin.cases (.ready value) fun _ => .var name) Fin.elim0)
        else none }
    | .pair => some {
      term i _ value :=
        if i == 0 then .node .first (fun _ => .ready value) Fin.elim0
        else .node .second (fun _ => .ready value) Fin.elim0
      body i _ _ _ := Fin.elim0 i }
    | _ => none

end FreeFoil.Examples.NbEDemos.Monolith

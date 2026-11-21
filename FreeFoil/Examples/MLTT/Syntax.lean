import FreeFoil
import FreeFoil.Derive

namespace FreeFoil.Examples.MLTT

inductive Pattern where
  | wildcard | variable | pair (left right : Pattern)
  deriving DecidableEq

def Pattern.binders : Pattern → Nat
  | .wildcard => 0
  | .variable => 1
  | .pair left right => left.binders + right.binders

inductive NamedTerm where
  | var (name : String)
  | pi (domain : NamedTerm) (codomain : BoundSyntax Pattern Pattern.binders NamedTerm)
  | sigma (domain : NamedTerm) (codomain : BoundSyntax Pattern Pattern.binders NamedTerm)
  | lam (body : BoundSyntax Pattern Pattern.binders NamedTerm)
  | letIn (value : NamedTerm) (body : BoundSyntax Pattern Pattern.binders NamedTerm)
  | app (fn arg : NamedTerm)
  | pair (fst snd : NamedTerm)
  | first (term : NamedTerm)
  | second (term : NamedTerm)
  | univ
  | unitType
  | unitVal
  | idType (type left right : NamedTerm)
  | refl (term : NamedTerm)
  | elimId (motive base path : NamedTerm)
  | ann (term type : NamedTerm)

derive_free_foil NamedTerm with Pattern, Pattern.binders

namespace Raw

def wildcard : Binder sig String := ⟨.wildcard, [], rfl⟩

def varPattern (name : String) : Binder sig String := ⟨.variable, [name], rfl⟩

def pairPattern (left right : Binder sig String) : Binder sig String :=
  ⟨.pair left.shape right.shape, left.names ++ right.names, by
    simp [sig, Pattern.binders, left.arity, right.arity]⟩

end Raw

/-- A binder of arity zero leaves its body's scope unchanged. -/
def wildcardBody (body : Term scope) : ScopedAST sig scope :=
  ⟨⟨.wildcard, [], rfl⟩, List.nodup_nil, body⟩

/-- A binder that binds just one identifier. -/
def variableBody (id : Nat) (body : Term (id :: scope)) : ScopedAST sig scope :=
  ⟨⟨.variable, [id], rfl⟩, by simp, body⟩

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
  | .pi domain ⟨shape, names, _, body⟩ =>
    let binder := (renderPattern shape names).1
    paren 0 s!"Π ({binder} : {renderTerm 0 domain}) → {renderTerm 0 body}"
  | .sigma domain ⟨shape, names, _, body⟩ =>
    let binder := (renderPattern shape names).1
    paren 0 s!"Σ ({binder} : {renderTerm 0 domain}) × {renderTerm 0 body}"
  | .lam ⟨shape, names, _, body⟩ =>
    paren 0 s!"λ {(renderPattern shape names).1} ⇒ {renderTerm 0 body}"
  | .letIn value ⟨shape, names, _, body⟩ =>
    paren 0 s!"let {(renderPattern shape names).1} = {renderTerm 0 value} in {renderTerm 0 body}"
  | .app fn arg => paren 1 s!"{renderTerm 1 fn} {renderTerm 2 arg}"
  | .pair fst snd => s!"({renderTerm 0 fst}, {renderTerm 0 snd})"
  | .first term => s!"π₁ {renderTerm 2 term}"
  | .second term => s!"π₂ {renderTerm 2 term}"
  | .univ => "𝕌"
  | .unitType => "𝟙"
  | .unitVal => "tt"
  | .idType type left right =>
    s!"Id({renderTerm 0 type}, {renderTerm 0 left}, {renderTerm 0 right})"
  | .refl term => s!"refl ({renderTerm 0 term})"
  | .elimId motive base path =>
    s!"J ({renderTerm 0 motive}, {renderTerm 0 base}, {renderTerm 0 path})"
  | .ann term type => s!"({renderTerm 0 term} : {renderTerm 0 type})"
termination_by structural value

def prettyRaw (term : Raw) : String := renderTerm 0 (NamedTerm.fromRaw term)

def prettyTerm (scope : Scope) (term : Term scope)
    (name : Name scope → String := fun name => s!"x{name.id}") : String :=
  renderTerm 0 (Term.toNamedTerm scope term name)

end FreeFoil.Examples.MLTT

import FreeFoil.Derive

namespace FreeFoil.Examples.DependentTypes

def arity (_ : Unit) : Nat := 1

namespace Surface

inductive NamedTerm where
  | var (name : String)
  | universe (level : Nat)
  | unitType
  | unitVal
  | pi (domain : NamedTerm) (codomain : BoundSyntax Unit arity NamedTerm)
  | sigma (domain : NamedTerm) (codomain : BoundSyntax Unit arity NamedTerm)
  | lam (domain : NamedTerm) (body : BoundSyntax Unit arity NamedTerm)
  | app (fn arg : NamedTerm)
  | pair (first second : NamedTerm)
  | first (pair : NamedTerm)
  | second (pair : NamedTerm)

derive_free_foil NamedTerm with Unit, arity

private def render (prec : Nat) (term : NamedTerm) : String :=
  let paren (own : Nat) (text : String) := if prec > own then s!"({text})" else text
  match term with
  | .var name => name
  | .universe level => s!"U {level}"
  | .unitType => "Unit"
  | .unitVal => "tt"
  | .pi domain ⟨(), names, arity, codomain⟩ =>
    let name := names[0]'(by simp [arity, DependentTypes.arity])
    paren 0 s!"({name} : {render 0 domain}) -> {render 0 codomain}"
  | .sigma domain ⟨(), names, arity, codomain⟩ =>
    let name := names[0]'(by simp [arity, DependentTypes.arity])
    paren 0 s!"({name} : {render 0 domain}) * {render 0 codomain}"
  | .lam domain ⟨(), names, arity, body⟩ =>
    let name := names[0]'(by simp [arity, DependentTypes.arity])
    paren 0 s!"\\({name} : {render 0 domain}). {render 0 body}"
  | .app fn arg => paren 1 s!"{render 1 fn} {render 2 arg}"
  | .pair first second => s!"({render 0 first}, {render 0 second})"
  | .first pair => paren 1 s!"first {render 2 pair}"
  | .second pair => paren 1 s!"second {render 2 pair}"
termination_by structural term

def pretty (term : Term scope) (name : Name scope → String) : String :=
  render 0 (Term.toNamedTerm scope term name)

end Surface

/-- Each computed type is a child in the same scope as its subject. Names get their
types from the typing context, and the types of the constants are fixed. -/
inductive NamedTerm where
  | var (name : String)
  | universe (level : Nat)
  | unitType
  | unitVal
  | pi (domain type : NamedTerm) (codomain : BoundSyntax Unit arity NamedTerm)
  | sigma (domain type : NamedTerm) (codomain : BoundSyntax Unit arity NamedTerm)
  | lam (domain type : NamedTerm) (body : BoundSyntax Unit arity NamedTerm)
  | app (fn arg type : NamedTerm)
  | pair (first second type : NamedTerm)
  | first (pair type : NamedTerm)
  | second (pair type : NamedTerm)

derive_free_foil NamedTerm with Unit, arity

abbrev Elaborated := Term

/-- Erase the type annotations while retaining the explicitly written domains. -/
def Elaborated.erase (term : Elaborated scope) : Surface.Term scope :=
  term.hoist (dst := Surface.sig) (fun shape => ⟨shape, rfl⟩) fun op fields children =>
    match op with
    | .universe level => Surface.Term.universe level
    | .unitType => Surface.Term.unitType
    | .unitVal => Surface.Term.unitVal
    | .pi => Surface.Term.pi (fields 0) (children 0)
    | .sigma => Surface.Term.sigma (fields 0) (children 0)
    | .lam => Surface.Term.lam (fields 0) (children 0)
    | .app => Surface.Term.app (fields 0) (fields 1)
    | .pair => Surface.Term.pair (fields 0) (fields 1)
    | .first => Surface.Term.first (fields 0)
    | .second => Surface.Term.second (fields 0)

def Elaborated.pretty (term : Elaborated scope) (name : Name scope → String) : String :=
  Surface.pretty term.erase name

end FreeFoil.Examples.DependentTypes

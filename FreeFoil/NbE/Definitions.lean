import FreeFoil.NbE

namespace FreeFoil.NbE

/-- Nonrecursive definitions in a scope, with the readback choice for that scope. -/
structure Definitions (sig : Signature) (scope : Scope) where
  private mk ::
  unfolding : Unfolding
  private lookup : Name scope → Option (Thunk sig scope)

/-- The scope's names start as neutrals. -/
def Definitions.empty : Definitions sig scope :=
  ⟨.unfolded, fun _ => none⟩

/-- Keep the same definitions and choose how to read them back. -/
def Definitions.withUnfolding (defs : Definitions sig scope) (mode : Unfolding) :
    Definitions sig scope :=
  { defs with unfolding := mode }

/-- Carry definitions into an extended scope, leaving its new names undefined. -/
def Definitions.sink (defs : Definitions sig source) (included : source ⊆ target) :
    Definitions sig target :=
  ⟨defs.unfolding, fun name => do
    let old ← Name.ofId source name.id
    let body ← defs.lookup old
    some (body.sink included)⟩

/-- Define a fresh name. Its suspended body captures the preceding definitions
and is scoped before the new name is introduced. -/
def Definitions.define (defs : Definitions sig scope) (name : Nat) (_fresh : name ∉ scope)
    (body : AST sig scope) : Definitions sig (name :: scope) :=
  have included : scope ⊆ name :: scope := fun {_} => List.mem_cons_of_mem _
  let outer := defs.sink included
  let captured := Thunk.syntax body fun ref =>
    match defs.lookup ref with
    | some body => .defined ref body
    | none => Thunk.var ref
  ⟨defs.unfolding, fun ref =>
    if ref.id == name then some (captured.sink included) else outer.lookup ref⟩

/-- Combine a language's rules with a definition context. The original context
still supplies the language's reduction and refinement rules. -/
def Rules.withDefinitions (rules : Rules sig Context) :
    Rules sig (fun scope => Context scope × Definitions sig scope) where
  reduce evaluator ctx := rules.reduce evaluator ctx.1
  extend evaluator ctx op terms index binder := do
    let inner ← rules.extend evaluator ctx.1 op terms index binder
    let defs := ctx.2.sink (fun {_} mem => List.mem_append_right _ mem)
    pure (inner, defs)
  refine evaluator ctx := rules.refine evaluator ctx.1
  isHead := rules.isHead
  eta op := (rules.eta op).map fun observers => {
    term i ctx := observers.term i ctx.1
    body i binder ctx := observers.body i binder ctx.1 }
  definition ctx name := (ctx.2.lookup name).orElse fun _ => rules.definition ctx.1 name
  unfolding ctx := ctx.2.unfolding
  isAnnotation := rules.isAnnotation
  refineWithFuel := rules.refineWithFuel.map fun refine {_} fuel evaluator ctx =>
    refine fuel evaluator ctx.1
  etaWithEvaluator op := (rules.etaWithEvaluator op).map fun observers => {
    term evaluator i ctx := observers.term evaluator i ctx.1
    body i binder evaluator ctx := observers.body i binder evaluator ctx.1 }

end FreeFoil.NbE

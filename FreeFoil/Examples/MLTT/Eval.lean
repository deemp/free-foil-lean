import FreeFoil.Examples.MLTT.Syntax

namespace FreeFoil.Examples.MLTT

inductive EvalError where
  | outOfFuel
  deriving Repr

abbrev Definitions (scope : Scope) := Name scope → Option (Term scope)

private def Pattern.arguments (shape : Pattern) (arg : Term scope) :
    Fin shape.binders → Term scope :=
  match shape with
  | .wildcard => Fin.elim0
  | .variable => fun _ => arg
  | .pair left right =>
    Fin.addCases (left.arguments (Term.first arg)) (right.arguments (Term.second arg))

/-- Open a binder by projecting its variables from one argument. -/
def instantiate (child : ScopedAST sig source) (target : Scope) (outer : source ⊆ target)
    (arg : Term target) : Term target :=
  child.instantiate target (.weakening outer) fun i =>
    child.binder.shape.arguments arg (Fin.cast child.binder.arity i)

/-- Weak-head normalization with a bound on recursive evaluation depth. -/
def whnf (scope : Scope) (defs : Definitions scope) (fuel : Nat) (term : Term scope) :
    Except EvalError (Term scope) :=
  match fuel with
  | 0 => .error .outOfFuel
  | fuel + 1 =>
    let reduce := whnf scope defs fuel
    match term.view with
    | .var name =>
      match defs name with
      | some value => reduce value
      | none => pure term
    | .node .app fields _ => do
      let fn ← reduce (fields 0)
      match fn.view with
      | .node .lam _ children => reduce (instantiate (children 0) scope (fun {_} mem => mem) (fields 1))
      | _ => pure (Term.app fn (fields 1))
    | .node .first fields _ => do
      let pair ← reduce (fields 0)
      match pair.view with
      | .node .pair fields _ => reduce (fields 0)
      | _ => pure (Term.first pair)
    | .node .second fields _ => do
      let pair ← reduce (fields 0)
      match pair.view with
      | .node .pair fields _ => reduce (fields 1)
      | _ => pure (Term.second pair)
    | .node .elimId fields _ => do
      let path ← reduce (fields 2)
      match path.view with
      | .node .refl _ _ => reduce (fields 1)
      | _ => pure (Term.elimId (fields 0) (fields 1) path)
    | .node .letIn fields children => reduce (instantiate (children 0) scope (fun {_} mem => mem) (fields 0))
    | .node .ann fields _ => reduce (fields 0)
    | _ => pure term

private def etaContract (scope : Scope) (term : Term scope) : Term scope :=
  match term.view with
  | .node .lam _ children => Id.run do
    let child := children 0
    let .variable := child.binder.shape | return term
    let [id] := child.binder.names | return term
    let .node .app fields _ := child.body.view | return term
    let .var arg := (fields 1).view | return term
    if arg.id == id then
      return ((fields 0).restrict scope).getD term
    return term
  | _ => term

/-- Full normalization, including under binders and function η-contraction. -/
def nf (scope : Scope) (defs : Definitions scope) (fuel : Nat) (term : Term scope) :
    Except EvalError (Term scope) :=
  match fuel with
  | 0 => .error .outOfFuel
  | fuel + 1 => do
    let head ← whnf scope defs (fuel + 1) term
    match head.view with
    | .var _ => pure head
    | .node op fields children =>
      let fields ← Vector.ofFnM fun i => nf scope defs fuel (fields i)
      let children ← Vector.ofFnM fun i => do
        let child := children i
        -- A sunk definition may have binders whose identifiers now belong to ambient names.
        let fresh := scope.freshen false child.binder.names
        let inner := fresh.val ++ scope
        let includeOuter : scope ⊆ inner := fun {_} mem => List.mem_append_right _ mem
        let args (index : Fin child.binder.names.length) : Term inner :=
          let index := Fin.cast fresh.property.1.symm index
          AST.var ⟨fresh.val[index], List.mem_append_left _ (List.getElem_mem index.isLt)⟩
        let body := child.instantiate inner (.weakening includeOuter) args
        let defs' (name : Name inner) : Option (Term inner) := do
          let outer ← Name.ofId scope name.id
          return (← defs outer).sink includeOuter
        let body ← nf inner defs' fuel body
        pure (⟨⟨child.binder.shape, fresh.val, fresh.property.1.trans child.binder.arity⟩,
          fresh.property.2.1, body⟩ : ScopedAST sig scope)
      pure (etaContract scope (AST.node op fields.get children.get))

/-- Definitional equality compares full normal forms up to α-equivalence. -/
def conv (scope : Scope) (defs : Definitions scope) (fuel : Nat) (left right : Term scope) :
    Except EvalError Bool := do
  let left ← nf scope defs fuel left
  let right ← nf scope defs fuel right
  pure (left.alphaEquiv right)

end FreeFoil.Examples.MLTT

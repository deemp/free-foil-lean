import FreeFoil.Examples.MLTT.Eval

namespace FreeFoil.Examples.MLTT

/-- Every name has a type and may have a definition for δ-reduction. -/
structure Context (scope : Scope) where
  typeOf : Name scope → Term scope
  definitions : Definitions scope

namespace Context

def empty : Context [] where
  typeOf name := nomatch name.property
  definitions name := nomatch name.property

/-- Add a local assumption or a definition at a caller-supplied fresh identifier. -/
def extend (ctx : Context scope) (id : Nat) (_fresh : id ∉ scope) (type : Term scope)
    (value : Option (Term scope) := none) : Context (id :: scope) :=
  let liftTerm : Term scope → Term (id :: scope) := AST.sink (fun {_} mem => List.mem_cons_of_mem _ mem)
  let outer (name : Name (id :: scope)) (ne : name.id ≠ id) : Name scope :=
    ⟨name.id, (List.mem_cons.mp name.property).resolve_left ne⟩
  { typeOf := fun name =>
      if ne : name.id ≠ id then liftTerm (ctx.typeOf (outer name ne)) else liftTerm type
    definitions := fun name =>
      if h : name.id ∈ scope then
        (ctx.definitions ⟨name.id, h⟩).map liftTerm
      else value.map liftTerm }

def addLocal (ctx : Context scope) (type : Term scope) : Context (scope.nextId :: scope) :=
  ctx.extend scope.nextId (scope.nextId_not_mem) type

end Context

inductive TypeError where
  | outOfFuel
  | evaluation (error : EvalError)
  | expectedType (description actual : String)
  | typeMismatch (expected actual : String)
  | cannotInferLambda
  deriving Repr

instance : ToString TypeError where
  toString
    | .outOfFuel => "type checking ran out of fuel"
    | .evaluation .outOfFuel => "evaluation ran out of fuel"
    | .expectedType description actual => s!"expected {description}, got {actual}"
    | .typeMismatch expected actual => s!"expected type {expected}, got {actual}"
    | .cannotInferLambda => "cannot infer the type of a lambda; add an ascription"

private def whnfIn (ctx : Context scope) (fuel : Nat) (term : Term scope) :
    Except TypeError (Term scope) :=
  (whnf scope ctx.definitions fuel term).mapError .evaluation

private def expected (what : String) (type : Term scope) : TypeError :=
  .expectedType what (prettyTerm scope type)

/-- The type of the identity eliminator's motive, Π (x : A) → Id(A, a, x) → 𝕌. -/
private def motiveType (scope : Scope) (type left : Term scope) : Term scope :=
  let x := scope.fresh
  let liftTerm : Term scope → Term (x.id :: scope) :=
    AST.sink (fun {_} mem => List.mem_cons_of_mem _ mem)
  let identity := Term.idType (liftTerm type) (liftTerm left) (AST.var x)
  Term.pi type (variableBody x.id (Term.pi identity (wildcardBody Term.univ)))

mutual

/-- Infer a type for a scoped MLTT term. Lambdas need an expected type or ascription. -/
def infer {scope : Scope} (ctx : Context scope) (fuel : Nat) (term : Term scope) :
    Except TypeError (Term scope) :=
  match fuel with
  | 0 => .error .outOfFuel
  | fuel + 1 => do
    match term.view with
    | .var name => pure (ctx.typeOf name)
    | .node .univ _ _ | .node .unitType _ _ => pure Term.univ
    | .node .unitVal _ _ => pure Term.unitType
    | .node .pi fields children | .node .sigma fields children =>
      let domain := fields 0
      check ctx fuel domain Term.univ
      let child := children 0
      let x := AST.var scope.fresh
      let ctx' := ctx.addLocal domain
      let body := instantiate child _ (fun {_} mem => List.mem_cons_of_mem _ mem) x
      check ctx' fuel body Term.univ
      pure Term.univ
    | .node .app fields _ =>
      let fnType ← whnfIn ctx fuel (← infer ctx fuel (fields 0))
      match fnType.view with
      | .node .pi parts children =>
        check ctx fuel (fields 1) (parts 0)
        pure (instantiate (children 0) scope (fun {_} mem => mem) (fields 1))
      | _ => throw (expected "a Π-type" fnType)
    | .node .first fields _ =>
      let pairType ← whnfIn ctx fuel (← infer ctx fuel (fields 0))
      match pairType.view with
      | .node .sigma parts _ => pure (parts 0)
      | _ => throw (expected "a Σ-type" pairType)
    | .node .second fields _ =>
      let pairType ← whnfIn ctx fuel (← infer ctx fuel (fields 0))
      match pairType.view with
      | .node .sigma _ children =>
        pure (instantiate (children 0) scope (fun {_} mem => mem) (Term.first (fields 0)))
      | _ => throw (expected "a Σ-type" pairType)
    | .node .pair fields _ =>
      let left ← infer ctx fuel (fields 0)
      let right ← infer ctx fuel (fields 1)
      pure (Term.sigma left (wildcardBody right))
    | .node .ann fields _ =>
      check ctx fuel (fields 1) Term.univ
      check ctx fuel (fields 0) (fields 1)
      pure (fields 1)
    | .node .letIn fields children =>
      let _ ← infer ctx fuel (fields 0)
      let child := children 0
      infer ctx fuel (instantiate child scope (fun {_} mem => mem) (fields 0))
    | .node .idType fields _ =>
      let type := fields 0
      check ctx fuel type Term.univ
      check ctx fuel (fields 1) type
      check ctx fuel (fields 2) type
      pure Term.univ
    | .node .refl fields _ =>
      let value := fields 0
      pure (Term.idType (← infer ctx fuel value) value value)
    | .node .elimId fields _ =>
      let motive := fields 0
      let path := fields 2
      let pathType ← whnfIn ctx fuel (← infer ctx fuel path)
      match pathType.view with
      | .node .idType parts _ =>
        let left := parts 1
        check ctx fuel motive (motiveType scope (parts 0) left)
        check ctx fuel (fields 1) (Term.app (Term.app motive left) (Term.refl left))
        pure (Term.app (Term.app motive (parts 2)) path)
      | _ => throw (expected "an identity type" pathType)
    | .node .lam _ _ => throw .cannotInferLambda
termination_by structural fuel

/-- Check a scoped MLTT term against an expected type. The projections inserted by
pattern binders are checked at their uses, following the upstream rules. -/
def check {scope : Scope} (ctx : Context scope) (fuel : Nat) (term type : Term scope) :
    Except TypeError Unit :=
  match fuel with
  | 0 => .error .outOfFuel
  | fuel + 1 => do
    let head ← whnfIn ctx (fuel + 1) type
    match term.view, head.view with
    | .node .lam _ children, .node .pi domains codomains =>
      let ctx' := ctx.addLocal (domains 0)
      let x := AST.var scope.fresh
      let outer : scope ⊆ scope.nextId :: scope := fun {_} mem => List.mem_cons_of_mem _ mem
      let child := children 0
      check ctx' fuel (instantiate child _ outer x) (instantiate (codomains 0) _ outer x)
    | .node .lam _ _, _ => throw (expected "a Π-type for a lambda" head)
    | .node .pair fields _, .node .sigma domains codomains =>
      check ctx fuel (fields 0) (domains 0)
      check ctx fuel (fields 1) (instantiate (codomains 0) scope (fun {_} mem => mem) (fields 0))
    | _, _ =>
      let actual ← infer ctx fuel term
      let equal ← (conv scope ctx.definitions fuel type actual).mapError .evaluation
      unless equal do
        throw (.typeMismatch (prettyTerm scope type) (prettyTerm scope actual))
termination_by structural fuel

end

/-- Validate a declaration's type and its value in the preceding context. -/
def checkDefinition (ctx : Context scope) (fuel : Nat) (type value : Term scope) :
    Except TypeError Unit := do
  check ctx fuel type Term.univ
  check ctx fuel value type

end FreeFoil.Examples.MLTT

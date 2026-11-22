import FreeFoil.Examples.DependentTypes.NbE

namespace FreeFoil.Examples.DependentTypes

inductive TypeError where
  | outOfFuel
  | evaluation (error : NbE.Error)
  | expectedType
  | expectedFunction
  | expectedPair
  | cannotInferPair
  | domainMismatch
  | typeMismatch
  deriving Repr

instance : ToString TypeError where
  toString
    | .outOfFuel => "elaboration ran out of fuel"
    | .evaluation .outOfFuel => "evaluation ran out of fuel"
    | .evaluation (.invalidBinder expected actual) =>
      s!"expected a binder with {expected} names, got {actual}"
    | .expectedType => "expected a type"
    | .expectedFunction => "expected a term of Π type"
    | .expectedPair => "expected a term of Σ type"
    | .cannotInferPair => "a pair needs an expected Σ type"
    | .domainMismatch => "the lambda domain does not match its expected Π type"
    | .typeMismatch => "the inferred type is not a subtype of the expected type"

private abbrev Result := Except TypeError

private def evaluate (operation : NbE.Result α) : Result α :=
  operation.mapError .evaluation

private def universeLevel (type : Value scope) : Result Nat :=
  match type with
  | .node (.universe level) _ _ => pure level
  | _ => throw .expectedType

private def evaluator (ctx : Typing scope) (fuel : Nat) : Evaluator scope :=
  ⟨NbE.force rules fuel ctx⟩

private def elaboratedBody (child : ScopedAST Surface.sig scope)
    (body : Elaborated (child.binder.names ++ scope)) : ScopedAST sig scope :=
  ⟨⟨(), child.binder.names, child.binder.arity⟩, child.distinct, body⟩

mutual

private def inferCore (ctx : Typing scope) (fuel : Nat) (term : Surface.Term scope) :
    Result (Elaborated scope × Value scope) :=
  match fuel with
  | 0 => .error .outOfFuel
  | fuel + 1 => do
    match term.view with
    | .var name => pure (.var name, ctx.typeOf name)
    | .node (.universe level) _ _ => pure (Term.universe level, universeValue (level + 1))
    | .node .unitType _ _ => pure (Term.unitType, universeValue 0)
    | .node .unitVal _ _ => pure (Term.unitVal, unitTypeValue)
    | .node .pi fields children | .node .sigma fields children =>
      let (domain, domainKind) ← inferCore ctx fuel (fields 0)
      let i ← universeLevel domainKind
      let domainValue ← evaluate (eval ctx fuel domain)
      let child := children 0
      let inner := ctx.assume child.binder.names domainValue
      let (codomain, codomainKind) ← inferCore inner fuel child.body
      let j ← universeLevel codomainKind
      let child := elaboratedBody child codomain
      let level := max i j
      let type := Term.universe level
      let op := match term.view with
        | .node .pi _ _ => Term.pi
        | _ => Term.sigma
      pure (op domain type child, universeValue level)
    | .node .lam fields children =>
      let (domain, domainKind) ← inferCore ctx fuel (fields 0)
      let i ← universeLevel domainKind
      let domainValue ← evaluate (eval ctx fuel domain)
      let child := children 0
      let inner := ctx.assume child.binder.names domainValue
      let (body, bodyType) ← inferCore inner fuel child.body
      let bodyKind ← evaluate (typeOfValue (evaluator inner fuel) inner bodyType)
      let j ← universeLevel bodyKind
      let bodyType ← evaluate (quote inner fuel bodyType)
      let type := Term.pi domain (Term.universe (max i j)) (elaboratedBody child bodyType)
      pure (Term.lam domain type (elaboratedBody child body), ← evaluate (eval ctx fuel type))
    | .node .app fields _ =>
      let (fn, fnType) ← inferCore ctx fuel (fields 0)
      let .node .pi domains codomains := fnType | throw .expectedFunction
      let eval := evaluator ctx fuel
      let domain ← evaluate (eval.force (domains 0))
      let arg ← checkCore ctx fuel (fields 1) domain
      let type ← evaluate (instantiate eval (codomains 0) (.syntax arg NbE.Thunk.free))
      pure (Term.app fn arg (← evaluate (quote ctx fuel type)), type)
    | .node .first fields _ | .node .second fields _ =>
      let (pair, pairType) ← inferCore ctx fuel (fields 0)
      let .node .sigma domains codomains := pairType | throw .expectedPair
      let eval := evaluator ctx fuel
      let domain ← evaluate (eval.force (domains 0))
      let first := Term.first pair (← evaluate (quote ctx fuel domain))
      match term.view with
      | .node .first _ _ => pure (first, domain)
      | _ =>
        let type ← evaluate (instantiate eval (codomains 0) (.syntax first NbE.Thunk.free))
        pure (Term.second pair (← evaluate (quote ctx fuel type)), type)
    | .node .pair _ _ => throw .cannotInferPair
termination_by structural fuel

private def checkCore (ctx : Typing scope) (fuel : Nat) (term : Surface.Term scope) (type : Value scope) :
    Result (Elaborated scope) :=
  match fuel with
  | 0 => .error .outOfFuel
  | fuel + 1 => do
    match term.view, type with
    | .node .lam fields children, .node .pi domains codomains =>
      let (domain, kind) ← inferCore ctx fuel (fields 0)
      let _ ← universeLevel kind
      let actual ← evaluate (eval ctx fuel domain)
      let expected ← evaluate ((evaluator ctx fuel).force (domains 0))
      unless ← evaluate (NbE.conv rules fuel ctx actual expected) do throw .domainMismatch
      let child := children 0
      let inner := ctx.assume child.binder.names actual
      let codomain := codomains 0
      let arity : child.binder.names.length = codomain.binder.names.length := by
        rw [child.binder.arity, codomain.binder.arity]
      let bodyType ← evaluate ((evaluator inner fuel).force (codomain.openWith child.binder.names arity))
      let body ← checkCore inner fuel child.body bodyType
      pure (Term.lam domain (← evaluate (quote ctx fuel type)) (elaboratedBody child body))
    | .node .pair fields _, .node .sigma domains codomains =>
      let eval := evaluator ctx fuel
      let domain ← evaluate (eval.force (domains 0))
      let first ← checkCore ctx fuel (fields 0) domain
      let codomain ← evaluate (instantiate eval (codomains 0) (.syntax first NbE.Thunk.free))
      let second ← checkCore ctx fuel (fields 1) codomain
      pure (Term.pair first second (← evaluate (quote ctx fuel type)))
    | .node .pair _ _, _ => throw .expectedPair
    | _, _ =>
      let (term, actual) ← inferCore ctx fuel term
      unless ← evaluate (isSubtype ctx fuel actual type) do throw .typeMismatch
      pure term
termination_by structural fuel

end

/-- Infer a semantic type and attach scope-checked types to the term's nodes.
Refresh binders first because weakening may put their old identifiers in scope. -/
def infer (ctx : Typing scope) (fuel : Nat) (term : Surface.Term scope) :
    Except TypeError (Elaborated scope × Value scope) :=
  inferCore ctx fuel (term.refresh scope)

/-- Check a scoped term against an expected semantic type. -/
def check (ctx : Typing scope) (fuel : Nat) (term : Surface.Term scope) (type : Value scope) :
    Except TypeError (Elaborated scope) :=
  checkCore ctx fuel (term.refresh scope) type

def elaborateScoped (ctx : Typing scope) (fuel : Nat) (term type : Surface.Term scope) :
    Except TypeError (Elaborated scope × Elaborated scope) := do
  let (type, kind) ← infer ctx fuel type
  let _ ← universeLevel kind
  let typeValue ← evaluate (eval ctx fuel type)
  pure (← check ctx fuel term typeValue, type)

end FreeFoil.Examples.DependentTypes

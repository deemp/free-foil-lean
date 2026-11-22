import FreeFoil.Examples.DependentTypes.Syntax
import FreeFoil.NbE.Conversion

namespace FreeFoil.Examples.DependentTypes

abbrev Value := NbE.Value sig
abbrev Thunk := NbE.Thunk sig
abbrev Closure := NbE.Closure sig
abbrev Evaluator := NbE.Evaluator sig

/-- The type of each name is a semantic value in the current scope. -/
structure Typing (scope : Scope) where
  typeOf : Name scope → Value scope

def Typing.empty : Typing [] := ⟨fun name => nomatch name.property⟩

def Typing.assume (ctx : Typing scope) (names : List Nat) (type : Value scope) :
    Typing (names ++ scope) :=
  let weaken := NbE.Value.sink (sig := sig) (source := scope) (target := names ++ scope)
  let included : scope ⊆ names ++ scope := fun {_} => List.mem_append_right names
  ⟨fun name =>
    if bound : name.id ∈ names then
      weaken type included
    else
      weaken (ctx.typeOf ⟨name.id, (List.mem_append.mp name.property).resolve_left bound⟩) included⟩

def universeValue (level : Nat) : Value scope := .node (.universe level) Fin.elim0 Fin.elim0

def unitTypeValue : Value scope := .node .unitType Fin.elim0 Fin.elim0

private def unitVal : Value scope := .node .unitVal Fin.elim0 Fin.elim0

private def boundName (binder : Binder sig Nat) : Name (binder.names ++ scope) :=
  have bound : 0 < binder.names.length := by rw [binder.arity]; simp [arity]
  ⟨binder.names[0], List.mem_append_left _ (List.getElem_mem bound)⟩

def instantiate (evaluator : Evaluator scope) (body : Closure scope) (arg : Thunk scope) :
    NbE.Result (Value scope) :=
  evaluator.instantiateAtArity body (fun _ : Fin 1 => arg)

private def typeOfNode (op : Op) (fields : Fin (sig.terms op) → Thunk scope) : Thunk scope :=
  match op with
  | .universe level => .ready (universeValue (level + 1))
  | .unitType => .ready (universeValue 0)
  | .unitVal => .ready unitTypeValue
  | .lam | .pi | .sigma | .first | .second => fields 1
  | .app | .pair => fields 2

def typeOfValue (evaluator : Evaluator scope) (ctx : Typing scope) :
    Value scope → NbE.Result (Value scope)
  | .var name => pure (ctx.typeOf name)
  | .node op fields _ => evaluator.force (typeOfNode op fields)
  | .glued _ folded _ => typeOfValue evaluator ctx folded

private def firstOf (pair type : Thunk scope) : Thunk scope :=
  .node .first (Fin.cases pair fun _ => type) Fin.elim0

private def secondOf (pair type : Thunk scope) : Thunk scope :=
  .node .second (Fin.cases pair fun _ => type) Fin.elim0

private def application (fn arg type : Thunk scope) : Thunk scope :=
  .node .app (Fin.cases fn (Fin.cases arg fun _ => type)) Fin.elim0

private def reductionRules : NbE.Rules sig Typing where
  reduce evaluator _ op fields children :=
    match op with
    | .app => evaluator.eliminate .app fields children 0 fun
      | .node .lam _ bodies => some <$> instantiate evaluator (bodies 0) (fields 1)
      | _ => pure none
    | .first => evaluator.eliminate .first fields children 0 fun
      | .node .pair parts _ => some <$> evaluator.force (parts 0)
      | _ => pure none
    | .second => evaluator.eliminate .second fields children 0 fun
      | .node .pair parts _ => some <$> evaluator.force (parts 1)
      | _ => pure none
    | _ => pure none
  extend evaluator ctx op fields index binder :=
    match op with
    | .pi | .sigma | .lam => ctx.assume binder.names <$> evaluator.force (fields 0)
    | .universe _ | .unitType | .unitVal | .app | .pair | .first | .second => Fin.elim0 index
  isHead op i := match op with
    | .app | .first | .second => i == 0
    | _ => false
  isAnnotation op i := match op with
    | .lam | .pi | .sigma | .first | .second => i == 1
    | .app | .pair => i == 2
    | _ => false

private def evaluator (fuel : Nat) (ctx : Typing scope) : Evaluator scope :=
  ⟨NbE.force reductionRules fuel ctx⟩

/-- Construct the unique inhabitant, if the semantic type is a singleton.
Looking at the codomain after instantiation accounts for substitution that
turns a previously neutral type into Unit. -/
private def singleton (fuel : Nat) (ctx : Typing scope) (type : Value scope) :
    NbE.Result (Option (Value scope)) :=
  match fuel with
  | 0 => .error .outOfFuel
  | fuel + 1 => do
    match type with
    | .node .unitType _ _ => pure (some unitVal)
    | .node .pi fields children =>
      let domain ← (evaluator fuel ctx).force (fields 0)
      let codomain := children 0
      let binder := codomain.freshBinder
      let inner := ctx.assume binder.val.names domain
      let codomain ← (evaluator fuel inner).force
        (codomain.openWith binder.val.names binder.property.1)
      let some body ← singleton fuel inner codomain | return none
      let body ← NbE.quote reductionRules fuel inner body
      let closure : Closure scope := .mk ⟨binder.val, binder.property.2.1, body⟩ NbE.Thunk.free
      return some (.node .lam (Fin.cases (fields 0) fun _ => .ready type) fun _ => closure)
    | .node .sigma fields children =>
      let eval := evaluator fuel ctx
      let domain ← eval.force (fields 0)
      let some first ← singleton fuel ctx domain | return none
      let codomain ← instantiate eval (children 0) (.ready first)
      let some second ← singleton fuel ctx codomain | return none
      return some (.node .pair
        (Fin.cases (.ready first) (Fin.cases (.ready second) fun _ => .ready type)) Fin.elim0)
    | _ => pure none
termination_by structural fuel

private def refine (fuel : Nat) (evaluator : Evaluator scope) (ctx : Typing scope)
    (value : Value scope) : NbE.Result (Value scope) := do
  let type ← match value with
    | .var name => pure (ctx.typeOf name)
    | .node op fields _ =>
      match op with
      | .app | .first | .second => evaluator.force (typeOfNode op fields)
      | _ => return value
    | _ => return value
  return (← singleton fuel ctx type).getD value

def rules : NbE.Rules sig Typing := { reductionRules with
  refineWithFuel := some refine
  etaWithEvaluator op := match op with
    | .lam => some {
      term evaluator _ ctx other := do
        let .node .pi fields _ ← typeOfValue evaluator ctx other | return none
        return some (fields 0)
      body _ binder evaluator ctx other := do
        let .node .pi _ children ← typeOfValue evaluator ctx other | return none
        let arg := NbE.Thunk.var (boundName binder)
        let type ← instantiate evaluator (children 0) arg
        return some (application (.ready other) arg (.ready type)) }
    | .pair => some {
      term evaluator i ctx other := do
        let .node .sigma fields children ← typeOfValue evaluator ctx other | return none
        let head := NbE.Thunk.ready other
        let first := firstOf head (fields 0)
        if i == 0 then return some first
        let type ← instantiate evaluator (children 0) first
        return some (secondOf head (.ready type))
      body i _ _ _ _ := Fin.elim0 i }
    | _ => none }

def eval (ctx : Typing scope) (fuel : Nat) (term : Elaborated scope) : NbE.Result (Value scope) :=
  NbE.eval rules fuel ctx term

def quote (ctx : Typing scope) (fuel : Nat) (value : Value scope) : NbE.Result (Elaborated scope) :=
  NbE.quote rules fuel ctx value

def nf (ctx : Typing scope) (fuel : Nat) (term : Elaborated scope) : NbE.Result (Elaborated scope) :=
  NbE.nf rules fuel ctx term

def whnf (ctx : Typing scope) (fuel : Nat) (term : Elaborated scope) : NbE.Result (Elaborated scope) :=
  NbE.whnf rules fuel ctx term

def convertible (ctx : Typing scope) (fuel : Nat) (left right : Elaborated scope) :
    NbE.Result Bool :=
  NbE.convertible rules fuel ctx left right

private def subtypeBinders (compare : ∀ {scope}, Typing scope → Value scope → Value scope →
      NbE.Result Bool) (ctx : Typing scope) (fuel : Nat)
    (lowerDomain upperDomain : Thunk scope) (lowerBody upperBody : Closure scope)
    (contravariant : Bool) : NbE.Result Bool := do
  let eval := evaluator fuel ctx
  let lowerDomain ← eval.force lowerDomain
  let upperDomain ← eval.force upperDomain
  let (small, big) := if contravariant then (upperDomain, lowerDomain) else (lowerDomain, upperDomain)
  unless ← compare ctx small big do return false
  let binder := lowerBody.freshBinder
  let inner := ctx.assume binder.val.names small
  let eval := evaluator fuel inner
  let lower ← eval.force (lowerBody.openWith binder.val.names binder.property.1)
  let upperArity : binder.val.names.length = upperBody.binder.names.length := by
    rw [binder.val.arity, upperBody.binder.arity]
  let upper ← eval.force (upperBody.openWith binder.val.names upperArity)
  compare inner lower upper

/-- Universes are cumulative, Π domains are contravariant and Σ domains are
covariant. Compare all other forms by ordinary conversion. -/
def isSubtype (ctx : Typing scope) (fuel : Nat) (lower upper : Value scope) : NbE.Result Bool :=
  match fuel with
  | 0 => .error .outOfFuel
  | fuel + 1 => do
    let compare := fun {scope} (ctx : Typing scope) l u => isSubtype ctx fuel l u
    match lower, upper with
    | .node (.universe l) _ _, .node (.universe u) _ _ => return l ≤ u
    | .node .pi lowerFields lowerChildren, .node .pi upperFields upperChildren =>
      subtypeBinders compare ctx fuel (lowerFields 0) (upperFields 0)
        (lowerChildren 0) (upperChildren 0) true
    | .node .sigma lowerFields lowerChildren, .node .sigma upperFields upperChildren =>
      subtypeBinders compare ctx fuel (lowerFields 0) (upperFields 0)
        (lowerChildren 0) (upperChildren 0) false
    | _, _ => NbE.conv rules (fuel + 1) ctx lower upper
termination_by structural fuel

end FreeFoil.Examples.DependentTypes

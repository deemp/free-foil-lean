import FreeFoil.Examples.LambdaPi

namespace FreeFoil.Benchmarks.NbEBaselines

open FreeFoil.Examples.LambdaPi

private inductive Thunk (scope : Scope) where
  | neutral (name : Name scope)
  | syntax {source : Scope} (term : Term source) (env : Name source → Thunk scope)

private def Thunk.sink (thunk : Thunk source) (included : source ⊆ target) : Thunk target :=
  match thunk with
  | .neutral name => .neutral (name.sink included)
  | .syntax term env => .syntax term fun name => (env name).sink included

private structure Closure (scope : Scope) where
  source : Scope
  child : ScopedAST sig source
  env : Name source → Thunk scope

private inductive Value (scope : Scope) where
  | var (name : Name scope)
  | app (fn : Value scope) (arg : Thunk scope)
  | lam (body : Closure scope)
  | pi (domain : Thunk scope) (body : Closure scope)
  | univ

private def extend (env : Name source → Thunk scope) (names : List Nat)
    (args : Fin names.length → Thunk scope) (name : Name (names ++ source)) : Thunk scope :=
  if bound : name.id ∈ names then
    args ⟨names.idxOf name.id, List.idxOf_lt_length_of_mem bound⟩
  else
    env ⟨name.id, (List.mem_append.mp name.property).resolve_left bound⟩

private def force (fuel : Nat) (thunk : Thunk scope) : Except String (Value scope) :=
  match fuel with
  | 0 => throw "monomorphic evaluation ran out of fuel"
  | fuel + 1 => do
    match thunk with
    | .neutral name => pure (.var name)
    | .syntax term env =>
      match term.view with
      | .var name => force fuel (env name)
      | .node .app parts _ =>
        let arg := Thunk.syntax (parts 1) env
        match ← force fuel (.syntax (parts 0) env) with
        | .lam ⟨_, child, captured⟩ =>
          unless child.binder.shape == .variable do
            throw "monomorphic benchmark expects a single-variable lambda pattern"
          force fuel (.syntax child.body (extend captured child.binder.names (fun _ => arg)))
        | fn => pure (.app fn arg)
      | .node .lam _ children => pure (.lam ⟨_, children 0, env⟩)
      | .node .pi parts children => pure (.pi (.syntax (parts 0) env) ⟨_, children 0, env⟩)
      | .node .univ _ _ => pure .univ
      | _ => throw "monomorphic benchmark expects λ, application, Π or universe"
termination_by structural fuel

private def quote (fuel : Nat) (value : Value scope) : Except String (Term scope) :=
  match fuel with
  | 0 => throw "monomorphic readback ran out of fuel"
  | fuel + 1 => do
    match value with
    | .var name => pure (.var name)
    | .app fn arg => pure (Term.app (← quote fuel fn) (← quote fuel (← force fuel arg)))
    | .lam body => pure (Term.lam (← quoteBody (quote fuel) fuel body))
    | .pi domain body =>
      pure (Term.pi (← quote fuel (← force fuel domain)) (← quoteBody (quote fuel) fuel body))
    | .univ => pure Term.univ
where
  quoteBody (quoteValue : ∀ {inner}, Value inner → Except String (Term inner)) (fuel : Nat)
      (closure : Closure scope) : Except String (ScopedAST sig scope) := do
    let ⟨source, child, env⟩ := closure
    let names := scope.freshen false child.binder.names
    let binder : Binder sig Nat := ⟨child.binder.shape, names.val, names.property.1.trans child.binder.arity⟩
    let outer (name : Name source) :=
      (env name).sink (fun {_} mem => List.mem_append_right names.val mem)
    let arg (i : Fin child.binder.names.length) : Thunk (names.val ++ scope) :=
      let j := Fin.cast names.property.1.symm i
      .neutral ⟨names.val[j], List.mem_append_left _ (List.getElem_mem j.isLt)⟩
    let body ← force fuel (.syntax child.body (extend outer child.binder.names arg))
    pure ⟨binder, names.property.2.1, ← quoteValue body⟩

/-- Hand-written semantic constructors over the same λΠ AST as the generic normalizer. -/
def monomorphic (fuel : Nat) (term : Term scope) : Except String (Term scope) :=
  force fuel (.syntax term Thunk.neutral) >>= quote fuel

-- Materialize the rebuilt nodes and reuse substituted arguments. Stacking lazy
-- child functions across successive substitutions repeats work at each access.
private def substitute (term : Term source) (target : Scope)
    (subst : Substitution sig source target) : Term target :=
  term.fold
    (Term := fun s => (t : Scope) → Substitution sig s t → Term t)
    (Child := fun s => (t : Scope) → Substitution sig s t → ScopedAST sig t)
    (fun name _ sigma => sigma.lookup name)
    (fun binder _ body scope sigma =>
      let names := scope.freshen false binder.names
      let freshBinder : Binder sig Nat := ⟨binder.shape, names.val, names.property.1.trans binder.arity⟩
      let outer : Substitution sig _ (names.val ++ scope) :=
        .mapping fun name => (sigma.lookup name).sink (fun {_} mem => List.mem_append_right _ mem)
      let args (i : Fin binder.names.length) : Term (names.val ++ scope) :=
        let j := Fin.cast names.property.1.symm i
        .var ⟨names.val[j], List.mem_append_left _ (List.getElem_mem j.isLt)⟩
      ⟨freshBinder, names.property.2.1, body _ (outer.extend binder.names args)⟩)
    (fun op terms children scope sigma =>
      let terms := Vector.ofFn (fun i => terms i scope sigma)
      let children := Vector.ofFn (fun i => children i scope sigma)
      AST.node op terms.get children.get)
    target subst

private def substitutionHead (fuel : Nat) (term : Term scope) : Except String (Term scope) :=
  match fuel with
  | 0 => throw "substitution ran out of fuel"
  | fuel + 1 => do
    match term.view with
    | .node .app terms _ =>
      let fn ← substitutionHead fuel (terms 0)
      let arg := terms 1
      let .node .lam _ children := fn.view | return Term.app fn arg
      let child := children 0
      unless child.binder.shape == .variable do
        throw "substitution benchmark expects a single-variable lambda pattern"
      let subst := Substitution.identity.extend child.binder.names fun _ => arg
      substitutionHead fuel (substitute child.body scope subst)
    | .node .lam _ _ | .node .pi _ _ | .node .univ _ _ | .var _ => pure term
    | _ => throw "substitution benchmark expects λ, application, Π or universe"
termination_by structural fuel

/-- Full normalization by capture-avoiding substitution on the same λΠ AST. -/
def substitution (fuel : Nat) (term : Term scope) : Except String (Term scope) :=
  match fuel with
  | 0 => throw "substitution readback ran out of fuel"
  | fuel + 1 => do
    let head ← substitutionHead (fuel + 1) term
    match head.view with
    | .var _ => pure head
    | .node op parts children =>
      let parts ← Vector.ofFnM fun i => substitution fuel (parts i)
      let children ← Vector.ofFnM fun i => do
        let child := children i
        let body ← substitution fuel child.body
        pure { child with body }
      pure (.node op parts.get children.get)
termination_by structural fuel

end FreeFoil.Benchmarks.NbEBaselines

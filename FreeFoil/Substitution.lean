import FreeFoil.AST

namespace FreeFoil

/-- A total map from source names to target terms, with an explicit weakening fast path. -/
inductive Substitution (sig : Signature) (source target : Scope) where
  | weakening (h : source ⊆ target)
  | mapping (lookup : Name source → AST sig target)

namespace Substitution

variable {sig : Signature} {source target : Scope}

def lookup (subst : Substitution sig source target) (name : Name source) : AST sig target :=
  match subst with
  | .weakening h => .var (name.sink h)
  | .mapping lookup => lookup name

def identity : Substitution sig source source := .weakening fun {_} mem => mem

/-- Extend a substitution with one argument per bound name, in binding order. -/
def extend (subst : Substitution sig source target) (names : List Nat)
    (args : Fin names.length → AST sig target) : Substitution sig (names ++ source) target :=
  .mapping fun name =>
    if bound : name.id ∈ names then
      args ⟨names.idxOf name.id, List.idxOf_lt_length_of_mem bound⟩
    else
      subst.lookup ⟨name.id, (List.mem_append.mp name.property).resolve_left bound⟩

end Substitution

namespace Scope

private def chooseId (force : Bool) (scope : Scope) (old : Nat) : { id : Nat // id ∉ scope } :=
  if keep : force = false ∧ old ∉ scope then
    ⟨old, keep.2⟩
  else
    ⟨nextId scope, nextId_not_mem scope⟩

/-- Allocate distinct names, keeping the old identifiers when possible unless `force` is set. -/
def freshen (force : Bool) (scope : Scope) (names : List Nat) :
    { ids : List Nat // ids.length = names.length ∧ ids.Nodup ∧ ∀ id ∈ ids, id ∉ scope } :=
  match names with
  | [] => ⟨[], by simp⟩
  | old :: rest =>
    let first := chooseId force scope old
    let tail := freshen force (first.val :: scope) rest
    ⟨first.val :: tail.val, by
      rcases tail.property with ⟨arity, distinct, fresh⟩
      refine ⟨by simp [arity], List.nodup_cons.mpr ⟨?_, distinct⟩, ?_⟩
      · intro mem
        exact fresh first.val mem (by simp)
      · intro id mem
        rcases List.mem_cons.mp mem with eq | memTail
        · rw [eq]
          exact first.property
        · exact fun memScope => fresh id memTail (List.mem_cons_of_mem _ memScope)⟩

end Scope

namespace AST

variable {sig : Signature} {source target : Scope}

private def substituteUsing (force : Bool) (term : AST sig source) (target : Scope)
    (subst : Substitution sig source target) : AST sig target :=
  term.fold
    (Term := fun s => (t : Scope) → Substitution sig s t → AST sig t)
    (Child := fun s => (t : Scope) → Substitution sig s t → ScopedAST sig t)
    (fun name _ env => env.lookup name)
    (fun binder _ body scope env =>
      let names := scope.freshen force binder.names
      let newBinder : Binder sig Nat := ⟨binder.shape, names.val, names.property.1.trans binder.arity⟩
      let lifted : Substitution sig _ (newBinder.names ++ scope) := .mapping fun name =>
        (env.lookup name).sink (fun {_} mem => List.mem_append_right _ mem)
      let extended := lifted.extend binder.names fun i =>
        let j : Fin newBinder.names.length := Fin.cast names.property.1.symm i
        .var ⟨newBinder.names[j], List.mem_append_left _ (List.getElem_mem j.isLt)⟩
      ⟨newBinder, names.property.2.1, body _ extended⟩)
    (fun op terms children scope env => .node op
      (fun i => terms i scope env) (fun i => children i scope env))
    target subst

/-- Apply a capture-avoiding substitution. A pure weakening reuses the original term. -/
def substitute (term : AST sig source) (target : Scope)
    (subst : Substitution sig source target) : AST sig target :=
  match subst with
  | .weakening h => term.sink h
  | .mapping _ => term.substituteUsing false target subst

/-- Apply a substitution, allocating canonical fresh names for each visited binder. -/
def substituteRefreshed (term : AST sig source) (target : Scope)
    (subst : Substitution sig source target) : AST sig target :=
  term.substituteUsing true target subst

/-- Canonically rename bound names while preserving free ones. -/
def refresh (scope : Scope) (term : AST sig scope) : AST sig scope :=
  term.substituteRefreshed scope .identity

end AST

/-- Substitute pattern arguments for bound names and use `env` for the outer names. -/
def ScopedAST.instantiate {sig : Signature} {source : Scope} (child : ScopedAST sig source)
    (target : Scope) (env : Substitution sig source target)
    (args : Fin child.binder.names.length → AST sig target) : AST sig target :=
  child.body.substitute target (env.extend child.binder.names args)

end FreeFoil

import FreeFoil.AST
import FreeFoil.Lexical

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

@[inline] private def liftBinder (subst : Substitution sig source target)
    (oldNames newNames : List Nat) (arity : newNames.length = oldNames.length) :
    Substitution sig (oldNames ++ source) (newNames ++ target) :=
  let lifted : Substitution sig source (newNames ++ target) := .mapping fun name =>
    (subst.lookup name).sink (fun {_} mem => List.mem_append_right _ mem)
  lifted.extend oldNames fun i =>
    let j : Fin newNames.length := Fin.cast arity.symm i
    .var ⟨newNames[j], List.mem_append_left _ (List.getElem_mem j.isLt)⟩

/-- Interpret the images of the substitution in the given lexical assignment. -/
def interpret (subst : Substitution sig source target) (env : Lexical.Assignment sig) :
    Lexical.Assignment sig :=
  fun id depth =>
    if mem : id ∈ source then
      Lexical.interpret (subst.lookup ⟨id, mem⟩).syntaxTree depth env
    else env id depth

private theorem interpret_liftBinder (subst : Substitution sig source target)
    (oldNames newNames : List Nat) (arity : newNames.length = oldNames.length)
    (distinct : newNames.Nodup) (fresh : ∀ id ∈ newNames, id ∉ target)
    (env : Lexical.Assignment sig) (depth : Nat) {id : Nat} (mem : id ∈ oldNames ++ source)
    (current : Nat) :
    (subst.liftBinder oldNames newNames arity).interpret (Lexical.under env newNames depth)
        id current =
      Lexical.under (subst.interpret env) oldNames depth id current := by
  by_cases bound : id ∈ oldNames
  · let j : Fin newNames.length :=
      Fin.cast arity.symm ⟨oldNames.idxOf id, List.idxOf_lt_length_of_mem bound⟩
    simp [interpret, mem, Lexical.under, bound, liftBinder, extend, lookup, AST.var, Name.id,
      Lexical.interpret, ← show j.val = oldNames.idxOf id from rfl, distinct.idxOf_getElem,
      arity]
  · have outer : id ∈ source := (List.mem_append.mp mem).resolve_left bound
    simp only [interpret, mem, dite_eq_left, liftBinder, extend, lookup, Name.id, bound,
      AST.sink, Lexical.under, outer]
    apply Lexical.interpret_congr _ (subst.lookup ⟨id, outer⟩).wellScoped
    intro name inTarget _
    have notBound : name ∉ newNames := fun h => fresh name h inTarget
    simp [Lexical.under, notBound]

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
      ⟨newBinder, names.property.2.1, body _ (env.liftBinder binder.names names.val names.property.1)⟩)
    (fun op terms children scope env => .node op
      (fun i => terms i scope env) (fun i => children i scope env))
    target subst

/-- Apply a capture-avoiding substitution. A pure weakening reuses the original term. -/
def substitute (term : AST sig source) (target : Scope)
    (subst : Substitution sig source target) : AST sig target :=
  match subst with
  | .weakening h => term.sink h
  | .mapping _ => term.substituteUsing false target subst

/-- Rename free names, refreshing any binders that would capture them. -/
def rename (term : AST sig source) (renameName : Name source → Name target) : AST sig target :=
  term.substitute target (.mapping fun name => .var (renameName name))

/-- Apply a substitution, allocating canonical fresh names for each visited binder. -/
def substituteRefreshed (term : AST sig source) (target : Scope)
    (subst : Substitution sig source target) : AST sig target :=
  term.substituteUsing true target subst

/-- Canonically rename bound names while preserving free ones. -/
def refresh (scope : Scope) (term : AST sig scope) : AST sig scope :=
  term.substituteRefreshed scope .identity

private theorem interpret_substituteUsing (force : Bool) (tree : Syntax sig Nat)
    (wf : tree.WellScoped source) (subst : Substitution sig source target)
    (depth : Nat) (env : Lexical.Assignment sig) :
    Lexical.interpret ((⟨tree, wf⟩ : AST sig source).substituteUsing force target subst).syntaxTree
        depth env =
      Lexical.interpret tree depth (subst.interpret env) := by
  induction tree generalizing source target depth env with
  | var id =>
    have mem : id ∈ source := wf
    simp only [Lexical.interpret, Substitution.interpret, mem, dite_eq_left]
    rfl
  | node op terms binders bodies ihTerms ihBodies =>
    let freshNames i := target.freshen force (binders i).names
    change Lexical.node op
      (fun i => Lexical.interpret (substituteUsing force ⟨terms i, wf.1 i⟩ target subst).syntaxTree
        depth env)
      (fun i => (binders i).shape)
      (fun i => Lexical.interpret (substituteUsing force ⟨bodies i, (wf.2 i).2⟩ _
        (subst.liftBinder (binders i).names (freshNames i).val (freshNames i).property.1)).syntaxTree
        (depth + sig.binders (binders i).shape) (Lexical.under env (freshNames i).val depth)) = _
    simp only [Lexical.interpret]
    congr 1
    · funext i
      exact ihTerms i (wf.1 i) subst depth env
    · funext i
      rw [ihBodies]
      apply Lexical.interpret_congr _ (wf.2 i).2
      intro _ mem current
      exact subst.interpret_liftBinder _ _ (freshNames i).property.1 (freshNames i).property.2.1
        (freshNames i).property.2.2 env depth mem current

/-- Substitution acts on the lexical interpretation by interpreting each image at the
depth of the occurrence. -/
theorem interpret_substitute (term : AST sig source) (subst : Substitution sig source target)
    (depth : Nat) (env : Lexical.Assignment sig) :
    Lexical.interpret (term.substitute target subst).syntaxTree depth env =
      Lexical.interpret term.syntaxTree depth (subst.interpret env) := by
  cases subst with
  | weakening included =>
    apply Lexical.interpret_congr _ term.wellScoped
    intro id mem current
    simp [Substitution.interpret, mem, Substitution.lookup, AST.var, Lexical.interpret]
    rfl
  | mapping lookup => exact interpret_substituteUsing false term.syntaxTree term.wellScoped _ depth env

/-- The lexical interpretation of substitution is independent of fresh-name choices. -/
theorem interpret_substituteRefreshed (term : AST sig source) (subst : Substitution sig source target)
    (depth : Nat) (env : Lexical.Assignment sig) :
    Lexical.interpret (term.substituteRefreshed target subst).syntaxTree depth env =
      Lexical.interpret term.syntaxTree depth (subst.interpret env) :=
  interpret_substituteUsing true term.syntaxTree term.wellScoped subst depth env

end AST

/-- Compose substitutions in application order. Apply `second` to the images of `first`. -/
def Substitution.compose {sig : Signature} {source middle target : Scope}
    (first : Substitution sig source middle) (second : Substitution sig middle target) :
    Substitution sig source target :=
  .mapping fun name => (first.lookup name).substitute target second

/-- Substitute pattern arguments for bound names and use `env` for the outer names. -/
def ScopedAST.instantiate {sig : Signature} {source : Scope} (child : ScopedAST sig source)
    (target : Scope) (env : Substitution sig source target)
    (args : Fin child.binder.names.length → AST sig target) : AST sig target :=
  child.body.substitute target (env.extend child.binder.names args)

end FreeFoil

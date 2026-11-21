import FreeFoil.Syntax

namespace FreeFoil

/-- A lexical interpretation for proofs about named syntax. Bound occurrences use absolute
binding levels, while free occurrences retain their original identifiers. -/
inductive Lexical (sig : Signature) where
  | free (id : Nat)
  | bound (level : Nat)
  | node (op : sig.Op)
      (terms : Fin (sig.terms op) → Lexical sig)
      (shapes : Fin (sig.scopes op) → sig.Pattern)
      (bodies : Fin (sig.scopes op) → Lexical sig)

namespace Lexical

variable {sig : Signature}

/-- An assignment interprets a name at the depth of the occurrence. -/
abbrev Assignment (sig : Signature) := Nat → Nat → Lexical sig

def freeAssignment : Assignment sig := fun id _ => .free id

/-- The nearest pattern wins. Levels decrease within the pattern so they agree with the
reverse numbering of the executable α-comparison's binding stack. -/
def under (env : Assignment sig) (names : List Nat) (depth : Nat) : Assignment sig :=
  fun id current =>
    if id ∈ names then .bound (depth + names.length - (names.idxOf id + 1))
    else env id current

def interpret (tree : Syntax sig Nat) (depth : Nat) (env : Assignment sig) : Lexical sig :=
  match tree with
  | .var id => env id depth
  | .node op terms binders bodies =>
    .node op
      (fun i => interpret (terms i) depth env)
      (fun i => (binders i).shape)
      (fun i => interpret (bodies i) (depth + sig.binders (binders i).shape)
        (under env (binders i).names depth))

theorem interpret_congr (tree : Syntax sig Nat) {scope : Scope} (wf : tree.WellScoped scope)
    (depth : Nat) {left right : Assignment sig}
    (agree : ∀ id ∈ scope, ∀ current, left id current = right id current) :
    interpret tree depth left = interpret tree depth right := by
  induction tree generalizing scope depth left right with
  | var id => exact agree id wf depth
  | node op terms binders bodies ihTerms ihBodies =>
    simp only [interpret]
    congr 1
    · funext i
      exact ihTerms i (wf.1 i) depth agree
    · funext i
      apply ihBodies i (wf.2 i).2
      intro id mem current
      by_cases bound : id ∈ (binders i).names
      · simp [under, bound]
      · simpa [under, bound] using agree id ((List.mem_append.mp mem).resolve_left bound) current

end Lexical
end FreeFoil

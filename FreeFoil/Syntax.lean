import FreeFoil.Scope

namespace FreeFoil

/-- A two-sorted syntax signature. Each operator has ordinary and scoped children.
A pattern shape determines how many names its scoped child binds, in binding order. -/
structure Signature where
  Op : Type
  Pattern : Type
  terms : Op → Nat
  scopes : Op → Nat
  binders : Pattern → Nat

/-- Pattern shape and its names, in binding order. -/
structure Binder (sig : Signature) (α : Type) where
  shape : sig.Pattern
  names : List α
  arity : names.length = sig.binders shape

/-- Syntax over a language signature, with names of type `α` and no scope index. -/
inductive Syntax (sig : Signature) (α : Type) where
  | var (name : α)
  | node (op : sig.Op)
      (terms : Fin (sig.terms op) → Syntax sig α)
      (binders : Fin (sig.scopes op) → Binder sig α)
      (bodies : Fin (sig.scopes op) → Syntax sig α)

namespace Syntax

/-- Scope membership follows the nearest binder, and names in one pattern are distinct. -/
def WellScoped : Syntax sig Nat → Scope → Prop
  | .var name, scope => name ∈ scope
  | .node _ terms binders bodies, scope =>
    (∀ i, WellScoped (terms i) scope) ∧
    (∀ i, (binders i).names.Nodup ∧ WellScoped (bodies i) ((binders i).names ++ scope))

theorem WellScoped.mono {term : Syntax sig Nat} {source target : Scope}
    (h : source ⊆ target) (wf : term.WellScoped source) : term.WellScoped target := by
  induction term generalizing source target with
  | var _ => exact h wf
  | node _ terms binders bodies ihTerms ihBodies =>
    exact ⟨fun i => ihTerms i h (wf.1 i), fun i =>
      ⟨(wf.2 i).1, ihBodies i (by
        intro name mem
        exact List.mem_append.mpr ((List.mem_append.mp mem).imp_right (fun mem => h mem))) (wf.2 i).2⟩⟩

/-- Check whether this numeric syntax is well scoped. -/
def check (term : Syntax sig Nat) (scope : Scope) : Decidable (term.WellScoped scope) :=
  match term with
  | .var name => inferInstanceAs (Decidable (name ∈ scope))
  | .node _ terms binders bodies =>
    letI (i : Fin _) := check (terms i) scope
    letI (i : Fin _) := check (bodies i) ((binders i).names ++ scope)
    inferInstanceAs (Decidable ((_ : Prop) ∧ (_ : Prop)))

end Syntax
end FreeFoil

import FreeFoil.Substitution
import FreeFoil.Lexical

namespace FreeFoil.AST

variable {sig : Signature}

private def alphaEq [DecidableEq sig.Op] [DecidableEq sig.Pattern]
    (left right : Syntax sig Nat) (bindings : List (Nat × Nat)) : Bool :=
  match left, right with
  | .var x, .var y =>
    match bindings.findIdx? (fun pair => pair.1 == x), bindings.findIdx? (fun pair => pair.2 == y) with
    | some i, some j => i == j
    | none, none => x == y
    | _, _ => false
  | .node op terms binders bodies, .node op' terms' binders' bodies' =>
    if h : op = op' then by
      subst op'
      exact (List.finRange (sig.terms op)).all (fun i => alphaEq (terms i) (terms' i) bindings) &&
        (List.finRange (sig.scopes op)).all fun i =>
          let binder := binders i
          let binder' := binders' i
          binder.shape == binder'.shape &&
            alphaEq (bodies i) (bodies' i) (binder.names.zip binder'.names ++ bindings)
    else false
  | _, _ => false
termination_by structural left

/-- Compare terms under corresponding binders, listed from innermost to outermost.
Identifiers outside those binders must agree. -/
def alphaEquivUnder [DecidableEq sig.Op] [DecidableEq sig.Pattern]
    (left : AST sig source) (right : AST sig target) (bindings : List (Nat × Nat)) : Bool :=
  alphaEq left.syntaxTree right.syntaxTree bindings

/-- Compare terms up to renaming of bound variables. Free identifiers must agree. -/
def alphaEquiv [DecidableEq sig.Op] [DecidableEq sig.Pattern]
    (left right : AST sig scope) : Bool :=
  left.alphaEquivUnder right []

private def stackAssignment (names : List Nat) : Lexical.Assignment sig :=
  Lexical.under Lexical.freeAssignment names 0

private theorem stackAssignment_append (inner outer : List Nat) :
    stackAssignment (sig := sig) (inner ++ outer) =
      Lexical.under (stackAssignment outer) inner outer.length := by
  funext id current
  by_cases inInner : id ∈ inner
  · simp [stackAssignment, Lexical.under, List.idxOf_append, inInner, Nat.add_comm]
  · by_cases inOuter : id ∈ outer
    · simp only [stackAssignment, Lexical.under, List.mem_append, inInner, inOuter, false_or,
        ite_true, ite_false, List.length_append, List.idxOf_append, Nat.zero_add]
      congr 1
      omega
    · simp [stackAssignment, Lexical.under, inInner, inOuter]

private theorem alphaVar_of_interpret_eq {x y : Nat} (bindings : List (Nat × Nat))
    (equal : stackAssignment (sig := sig) (bindings.map Prod.fst) x bindings.length =
      stackAssignment (bindings.map Prod.snd) y bindings.length) :
    (match bindings.findIdx? (fun pair => pair.1 == x),
        bindings.findIdx? (fun pair => pair.2 == y) with
     | some i, some j => i == j
     | none, none => x == y
     | _, _ => false) = true := by
  have lookup (names : List Nat) (id : Nat) :
      names.idxOf? id = if id ∈ names then some (names.idxOf id) else none := by
    split
    · rename_i mem
      exact List.findIdx?_eq_some_iff_findIdx_eq.mpr ⟨List.idxOf_lt_length_of_mem mem, rfl⟩
    · exact List.idxOf?_eq_none_iff.mpr ‹id ∉ names›
  have leftIndex : bindings.findIdx? (fun pair => pair.1 == x) =
      (bindings.map Prod.fst).idxOf? x := by simp [List.idxOf?, Function.comp_def]
  have rightIndex : bindings.findIdx? (fun pair => pair.2 == y) =
      (bindings.map Prod.snd).idxOf? y := by simp [List.idxOf?, Function.comp_def]
  rw [leftIndex, rightIndex, lookup, lookup]
  by_cases hx : x ∈ bindings.map Prod.fst <;> by_cases hy : y ∈ bindings.map Prod.snd
  · have ix := List.idxOf_lt_length_of_mem hx
    have iy := List.idxOf_lt_length_of_mem hy
    simp [stackAssignment, Lexical.under, hx, hy] at equal
    simp [hx, hy]
    simp only [List.length_map] at ix iy
    omega
  · simp [stackAssignment, Lexical.under, Lexical.freeAssignment, hx, hy] at equal
  · simp [stackAssignment, Lexical.under, Lexical.freeAssignment, hx, hy] at equal
  · simpa [stackAssignment, Lexical.under, Lexical.freeAssignment, hx, hy] using equal

private theorem alphaEq_of_interpret_eq [DecidableEq sig.Op] [DecidableEq sig.Pattern]
    (left right : Syntax sig Nat) (bindings : List (Nat × Nat))
    (equal : Lexical.interpret left bindings.length (stackAssignment (bindings.map Prod.fst)) =
      Lexical.interpret right bindings.length (stackAssignment (bindings.map Prod.snd))) :
    alphaEq left right bindings = true := by
  induction left generalizing right bindings with
  | var x =>
    cases right with
    | var y => exact alphaVar_of_interpret_eq bindings equal
    | node => simp [Lexical.interpret, stackAssignment, Lexical.under, Lexical.freeAssignment] at equal
              split at equal <;> contradiction
  | node op terms binders bodies ihTerms ihBodies =>
    cases right with
    | var y =>
      simp [Lexical.interpret, stackAssignment, Lexical.under, Lexical.freeAssignment] at equal
      split at equal <;> contradiction
    | node op' terms' binders' bodies' =>
      simp only [Lexical.interpret] at equal
      have opEqual := (Lexical.node.inj equal).1
      subst op'
      have ⟨termEqual, shapeEqual, bodyEqual⟩ := (Lexical.node.inj equal).2
      simp only [alphaEq, dite_true, Bool.and_eq_true, List.all_eq_true]
      constructor
      · intro i _
        exact ihTerms i (terms' i) bindings (congrFun (eq_of_heq termEqual) i)
      · intro i _
        have shape := congrFun (eq_of_heq shapeEqual) i
        have arity : (binders i).names.length = (binders' i).names.length := by
          rw [(binders i).arity, (binders' i).arity, shape]
        simp only [beq_iff_eq]
        refine ⟨shape, ihBodies i (bodies' i) _ ?_⟩
        have body := congrFun (eq_of_heq bodyEqual) i
        rw [List.map_append, List.map_append, List.map_fst_zip (Nat.le_of_eq arity),
          List.map_snd_zip (Nat.le_of_eq arity.symm), stackAssignment_append, stackAssignment_append,
          List.length_append, List.length_zip, arity, Nat.min_self,
          List.length_map, List.length_map]
        rw [Nat.add_comm, (binders' i).arity, ← shape]
        simpa only [shape] using body

/-- Agreement of lexical interpretations entails executable α-equivalence. -/
theorem alphaEquiv_of_lexical_eq [DecidableEq sig.Op] [DecidableEq sig.Pattern]
    (left right : AST sig scope)
    (equal : Lexical.interpret left.syntaxTree 0 Lexical.freeAssignment =
      Lexical.interpret right.syntaxTree 0 Lexical.freeAssignment) :
    left.alphaEquiv right = true := by
  exact alphaEq_of_interpret_eq left.syntaxTree right.syntaxTree [] equal

end FreeFoil.AST

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

private theorem alphaVar_iff_interpret_eq {x y : Nat} (bindings : List (Nat × Nat)) :
    (match bindings.findIdx? (fun pair => pair.1 == x),
        bindings.findIdx? (fun pair => pair.2 == y) with
     | some i, some j => i == j
     | none, none => x == y
     | _, _ => false) = true ↔
    stackAssignment (sig := sig) (bindings.map Prod.fst) x bindings.length =
      stackAssignment (bindings.map Prod.snd) y bindings.length := by
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
  by_cases hx : x ∈ bindings.map Prod.fst <;> by_cases hy : y ∈ bindings.map Prod.snd <;>
    simp [stackAssignment, Lexical.under, Lexical.freeAssignment, hx, hy]
  have ix := List.idxOf_lt_length_of_mem hx
  have iy := List.idxOf_lt_length_of_mem hy
  simp only [List.length_map] at ix iy
  omega

private theorem alphaEq_iff_interpret_eq [DecidableEq sig.Op] [DecidableEq sig.Pattern]
    (left right : Syntax sig Nat) (bindings : List (Nat × Nat)) :
    alphaEq left right bindings = true ↔
    Lexical.interpret left bindings.length (stackAssignment (bindings.map Prod.fst)) =
      Lexical.interpret right bindings.length (stackAssignment (bindings.map Prod.snd)) := by
  induction left generalizing right bindings with
  | var x =>
    cases right with
    | var y => exact alphaVar_iff_interpret_eq bindings
    | node =>
      simp [alphaEq, Lexical.interpret, stackAssignment, Lexical.under, Lexical.freeAssignment]
      split <;> simp
  | node op terms binders bodies ihTerms ihBodies =>
    cases right with
    | var y =>
      simp [alphaEq, Lexical.interpret, stackAssignment, Lexical.under, Lexical.freeAssignment]
      split <;> simp
    | node op' terms' binders' bodies' =>
      by_cases opEqual : op = op'
      · subst op'
        simp only [alphaEq, dite_true, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
          Lexical.interpret]
        have compareBody (i : Fin (sig.scopes op)) (shape : (binders i).shape = (binders' i).shape) :
            alphaEq (bodies i) (bodies' i) ((binders i).names.zip (binders' i).names ++ bindings) =
              true ↔
            Lexical.interpret (bodies i) (bindings.length + sig.binders (binders i).shape)
              (Lexical.under (stackAssignment (bindings.map Prod.fst)) (binders i).names
                bindings.length) =
            Lexical.interpret (bodies' i) (bindings.length + sig.binders (binders' i).shape)
              (Lexical.under (stackAssignment (bindings.map Prod.snd)) (binders' i).names
                bindings.length) := by
          have arity : (binders i).names.length = (binders' i).names.length := by
            rw [(binders i).arity, (binders' i).arity, shape]
          rw [ihBodies, List.map_append, List.map_append, List.map_fst_zip (Nat.le_of_eq arity),
            List.map_snd_zip (Nat.le_of_eq arity.symm), stackAssignment_append, stackAssignment_append,
            List.length_append, List.length_zip, arity, Nat.min_self,
            List.length_map, List.length_map]
          rw [Nat.add_comm, (binders' i).arity, shape]
        constructor
        · rintro ⟨termsAgree, childrenAgree⟩
          congr 1
          · funext i
            exact (ihTerms i (terms' i) bindings).mp (termsAgree i (List.mem_finRange i))
          · funext i
            exact (childrenAgree i (List.mem_finRange i)).1
          · funext i
            have ⟨shape, body⟩ := childrenAgree i (List.mem_finRange i)
            exact (compareBody i shape).mp body
        · intro equal
          have ⟨termEqual, shapeEqual, bodyEqual⟩ := (Lexical.node.inj equal).2
          constructor
          · intro i _
            exact (ihTerms i (terms' i) bindings).mpr (congrFun (eq_of_heq termEqual) i)
          · intro i _
            have shape := congrFun (eq_of_heq shapeEqual) i
            exact ⟨shape, (compareBody i shape).mpr (congrFun (eq_of_heq bodyEqual) i)⟩
      · simp only [alphaEq, opEqual, dite_false, Bool.false_eq_true, false_iff, Lexical.interpret]
        exact fun equal => opEqual (Lexical.node.inj equal).1

/-- The α-equivalence checker agrees with lexical equality. Bound occurrences use the level of
their nearest binder and position within its pattern. Free occurrences keep their identifiers. -/
theorem alphaEquiv_iff_lexical_eq [DecidableEq sig.Op] [DecidableEq sig.Pattern]
    (left right : AST sig scope) :
    left.alphaEquiv right = true ↔
    Lexical.interpret left.syntaxTree 0 Lexical.freeAssignment =
      Lexical.interpret right.syntaxTree 0 Lexical.freeAssignment :=
  alphaEq_iff_interpret_eq left.syntaxTree right.syntaxTree []

/-- Agreement of lexical interpretations entails executable α-equivalence. -/
theorem alphaEquiv_of_lexical_eq [DecidableEq sig.Op] [DecidableEq sig.Pattern]
    (left right : AST sig scope)
    (equal : Lexical.interpret left.syntaxTree 0 Lexical.freeAssignment =
      Lexical.interpret right.syntaxTree 0 Lexical.freeAssignment) :
    left.alphaEquiv right = true :=
  (alphaEquiv_iff_lexical_eq left right).mpr equal

end FreeFoil.AST

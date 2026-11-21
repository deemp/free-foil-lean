import FreeFoil.Substitution

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

end FreeFoil.AST

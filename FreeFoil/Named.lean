import FreeFoil.Substitution

namespace FreeFoil

inductive ResolveError (α : Type) where
  | unbound (name : α)
  | duplicateBinder (names : List α)
  deriving Repr

namespace AST

variable {sig : Signature} {α : Type}

/-- Resolve named syntax into a scope-safe AST. Free names can stand for scoped terms. -/
def fromNamedTerms [DecidableEq α] (scope : Scope) (resolve : α → Option (AST sig scope))
    (term : Syntax sig α) : Except (ResolveError α) (AST sig scope) :=
  match term with
  | .var name =>
    match resolve name with
    | some term => .ok term
    | none => .error (.unbound name)
  | .node op terms binders bodies => do
    let terms' ← Vector.ofFnM fun i => fromNamedTerms scope resolve (terms i)
    let children ← Vector.ofFnM fun i => do
      let binder := binders i
      if ¬binder.names.Nodup then
        throw (.duplicateBinder binder.names)
      let ids := scope.freshen true (binder.names.map fun _ => 0)
      have arity : ids.val.length = binder.names.length := ids.property.1.trans (List.length_map _)
      let binder' : Binder sig Nat := ⟨binder.shape, ids.val, arity.trans binder.arity⟩
      let resolve' (name : α) : Option (AST sig (binder'.names ++ scope)) :=
        if h : name ∈ binder.names then
          let i := binder.names.idxOf name
          have bound : i < binder'.names.length := arity ▸ List.idxOf_lt_length_of_mem h
          some (.var ⟨binder'.names[i], List.mem_append_left _ (List.getElem_mem bound)⟩)
        else
          (resolve name).map (AST.sink fun {_} mem => List.mem_append_right _ mem)
      let body ← fromNamedTerms (binder'.names ++ scope) resolve' (bodies i)
      pure (⟨binder', ids.property.2.1, body⟩ : ScopedAST sig scope)
    pure (.node op terms'.get children.get)
termination_by structural term

/-- Resolve named syntax into a scope-safe AST, looking up free variable names. -/
def fromNamed [DecidableEq α] (scope : Scope) (resolve : α → Option (Name scope))
    (term : Syntax sig α) : Except (ResolveError α) (AST sig scope) :=
  fromNamedTerms scope (fun name => (resolve name).map AST.var) term

/-- Resolve a term with no free variables. -/
def fromClosed [DecidableEq α] (term : Syntax sig α) : Except (ResolveError α) (AST sig []) :=
  fromNamed [] (fun _ => none) term

end AST

/-- Change the representation of all variable and binder names in a syntax tree. -/
def Syntax.mapNames (f : α → β) : Syntax sig α → Syntax sig β
  | .var name => .var (f name)
  | .node op terms binders bodies => .node op
      (fun i => (terms i).mapNames f)
      (fun i => ⟨(binders i).shape, (binders i).names.map f, by simp [(binders i).arity]⟩)
      (fun i => (bodies i).mapNames f)

/-- Convert to named syntax with canonical bound names and caller-supplied free names.
Use distinct strings for distinct free identifiers if the result will be resolved again. -/
def AST.toNamed {sig : Signature} (scope : Scope) (term : AST sig scope)
    (freeName : Name scope → String) : Syntax sig String :=
  let used := scope.attach.map freeName
  let maxLength := used.foldl (fun n s => max n s.length) 0
  let suffix := String.ofList (List.replicate (maxLength + 1) '_')
  (AST.refresh scope term).syntaxTree.mapNames fun id =>
    match Name.ofId scope id with
    | some name => freeName name
    | none =>
      let label := s!"x{id}"
      if used.contains label then label ++ suffix else label

end FreeFoil

import FreeFoil
import FreeFoil.Derive

namespace FreeFoil.Examples.SOAS

def bindingCount (count : Nat) : Nat := count

mutual
inductive NamedTerm where
  | var (name : String)
  | application (operator : String) (arguments : NamedArgs)
  | metavar (name : String) (arguments : NamedTerms)

inductive NamedArgs where
  | nil
  | cons (head : NamedArg) (tail : NamedArgs)

inductive NamedArg where
  | plain (term : NamedTerm)
  | bound (body : BoundSyntax Nat bindingCount NamedTerm)

inductive NamedTerms where
  | nil
  | cons (head : NamedTerm) (tail : NamedTerms)
end

inductive NamedType where
  | var (name : String)
  | function (domain codomain : NamedType)
  | product (left right : NamedType)

inductive NamedTyping where
  | judgment (term : NamedTerm) (type : NamedType)

derive_free_foil [NamedTerm, NamedArgs, NamedArg, NamedTerms, NamedType, NamedTyping]
  with Nat, bindingCount

def NamedTerm.operator (name : String) (arguments : List NamedArg) : NamedTerm :=
  .application name (arguments.foldr NamedArgs.cons .nil)

def NamedTerm.metavariable (name : String) (arguments : List NamedTerm) : NamedTerm :=
  .metavar name (arguments.foldr NamedTerms.cons .nil)

def NamedArg.bind (names : List String) (body : NamedTerm) : NamedArg :=
  .bound ⟨names.length, names, rfl, body⟩

private def parameters (names : List String) : Scope := List.range names.length

private def resolveParameter (names : List String) (name : String) :
    Option (Name (parameters names)) :=
  if bound : name ∈ names then
    some ⟨names.idxOf name, List.mem_range.mpr (List.idxOf_lt_length_of_mem bound)⟩
  else
    none

/-- A metavariable replacement, closed except for its ordered parameters. -/
structure MetaSubst where
  name : String
  replacement : ScopedAST sig []

def MetaSubst.fromNamed (name : String) (arguments : List String) (body : NamedTerm) :
    Except (ResolveError String) MetaSubst := do
  unless arguments.Nodup do throw (.duplicateBinder arguments)
  let binder : Binder sig Nat :=
    ⟨arguments.length, parameters arguments, List.length_range⟩
  let replacement ← NamedTerm.resolve (parameters arguments) (resolveParameter arguments) body
  pure ⟨name, ⟨binder, List.nodup_range, replacement.sink (by simp [binder])⟩⟩

/-- An equality whose two sides share the same ordered parameters. -/
structure Constraint where
  scope : Scope
  left : Term scope
  right : Term scope

def Constraint.fromNamed (names : List String) (left right : NamedTerm) :
    Except (ResolveError String) Constraint := do
  unless names.Nodup do throw (.duplicateBinder names)
  let scope := parameters names
  let resolve := resolveParameter names
  pure ⟨scope, ← NamedTerm.resolve scope resolve left, ← NamedTerm.resolve scope resolve right⟩

inductive SubstError where
  | arityMismatch (metavariable : String) (expected actual : Nat)
  | malformedArguments (metavariable : String)
  deriving Repr

private def readArguments {scope : Scope} (syntaxTree : Syntax sig Nat)
    (scopedProof : syntaxTree.WellScoped scope) : Option (List (Term scope)) :=
  match syntaxTree with
  | .node Op.NamedTerms.nil _ _ _ => some []
  | .node Op.NamedTerms.cons terms _ _ => do
    let rest ← readArguments (terms 1) (scopedProof.1 1)
    pure (⟨terms 0, scopedProof.1 0⟩ :: rest)
  | _ => none
termination_by structural syntaxTree

/-- Apply a simultaneous metavariable substitution. Arguments are substituted before
instantiation. The replacement body is inserted once, without recursing into it. -/
def applySubsts (scope : Scope) (substs : List MetaSubst) (term : Term scope) :
    Except SubstError (Term scope) :=
  term.fold
    (Term := fun scope => Except SubstError (Term scope))
    (Child := fun scope => Except SubstError (ScopedAST sig scope))
    (fun name => pure (AST.var name))
    (fun binder distinct body => do pure ⟨binder, distinct, ← body⟩)
    (fun {scope} op terms children => do
      let terms ← Vector.ofFnM terms
      let children ← Vector.ofFnM children
      match tag : op with
      | Op.NamedTerm.metavar name =>
        let argumentList := terms.get ⟨0, by simp [tag]⟩
        match substs.find? (·.name == name) with
        | none => pure (Term.NamedTerm.metavar name argumentList)
        | some entry =>
          let some arguments := readArguments argumentList.syntaxTree argumentList.wellScoped
            | throw (.malformedArguments name)
          let expected := entry.replacement.binder.names.length
          if arity : arguments.length = expected then
            pure (entry.replacement.instantiate scope (.weakening (by simp)) fun i =>
              arguments[Fin.cast arity.symm i])
          else
            throw (.arityMismatch name expected arguments.length)
      | _ => pure (AST.node op terms.get children.get))

/-- Match up to α-equivalence. Operators and metavariable identifiers are rigid, and
scoped arguments match by binder position. -/
def matchTerms (left right : Term scope) : Bool := left.alphaEquiv right

/-- Check each equality after applying the given simultaneous substitution. -/
def isSolutionFor (substs : List MetaSubst) (constraints : List Constraint) :
    Except SubstError Bool :=
  constraints.allM fun constraint => do
    let left ← applySubsts constraint.scope substs constraint.left
    let right ← applySubsts constraint.scope substs constraint.right
    pure (matchTerms left right)

/-- Failures of pattern unification. The scope error identifies an unavailable rigid variable. -/
inductive PatternError where
  | nonPattern (metavariable : String)
  | arityMismatch (metavariable : String) (expected actual : Nat)
  | rigidMismatch
  | cyclic (metavariable : String)
  | escapingVariable (metavariable : String) (id : Nat)
  | fuelExhausted
  | substitution (error : SubstError)
  | validationFailed
  deriving Repr

/-- A simultaneous substitution certified by the existing constraint checker. -/
structure PatternSolution (constraints : List Constraint) where
  substitutions : List MetaSubst
  satisfies : isSolutionFor substitutions constraints = .ok true

private structure PatternApplication where
  name : String
  arguments : List Nat
  distinct : arguments.Nodup

private def readPattern (name : String) (argumentList : Term scope) :
    Except PatternError PatternApplication := do
  let some terms := readArguments argumentList.syntaxTree argumentList.wellScoped
    | throw (.nonPattern name)
  let arguments ← terms.mapM fun term => match term.syntaxTree with
    | .var id => pure id
    | .node .. => throw (.nonPattern name)
  if distinct : arguments.Nodup then pure ⟨name, arguments, distinct⟩
  else throw (.nonPattern name)

private def patternHead (term : Term scope) : Except PatternError (Option PatternApplication) :=
  match term.view with
  | .node (Op.NamedTerm.metavar name) terms _ => some <$> readPattern name (terms 0)
  | _ => pure none

private inductive PatternUse where
  | variable (id : Nat)
  | metavar (application : PatternApplication) (localNames : Scope)

private def patternUses (tree : Syntax sig Nat) (wf : tree.WellScoped scope) (localNames : Scope) :
    Except PatternError (List PatternUse) :=
  match tree with
  | .var id => pure (if id ∈ localNames then [] else [.variable id])
  | .node (Op.NamedTerm.metavar name) terms _ _ => do
    let application ← readPattern name ⟨terms 0, wf.1 0⟩
    pure [.metavar application localNames]
  | .node op terms binders bodies => do
    let ordinary ← (List.finRange (sig.terms op)).mapM fun i =>
      patternUses (terms i) (wf.1 i) localNames
    let underBinders ← (List.finRange (sig.scopes op)).mapM fun i =>
      patternUses (bodies i) (wf.2 i).2 ((binders i).names ++ localNames)
    pure (ordinary.flatten ++ underBinders.flatten)
termination_by structural tree

private def freshPrefix : String := "?pattern"

private def validatePatterns (constraints : List Constraint) : Except PatternError Nat := do
  let mut arities : List (String × Nat) := []
  let mut next := 0
  for constraint in constraints do
    let left ← patternUses constraint.left.syntaxTree constraint.left.wellScoped []
    let right ← patternUses constraint.right.syntaxTree constraint.right.wellScoped []
    for use in left ++ right do
      if let .metavar pattern _ := use then
        let arity := pattern.arguments.length
        if let some (_, expected) := arities.find? (fun entry => entry.1 == pattern.name) then
          unless expected == arity do throw (.arityMismatch pattern.name expected arity)
        else
          arities := (pattern.name, arity) :: arities
          if pattern.name.startsWith freshPrefix then
            if let some index := (pattern.name.drop freshPrefix.length).toString.toNat? then
              next := max next (index + 1)
  pure next

private def alignChildren (left right : ScopedAST sig scope) : Except PatternError Constraint :=
  if shape : left.binder.shape = right.binder.shape then
    let names := scope.freshen true left.binder.names
    let target := names.val ++ scope
    let openChild (child : ScopedAST sig scope) (arity : child.binder.names.length = names.val.length) :=
      child.instantiate target (.weakening fun {_} mem => List.mem_append_right _ mem) fun i =>
        let j := Fin.cast arity i
        .var ⟨names.val[j], List.mem_append_left _ (List.getElem_mem j.isLt)⟩
    have rightArity : right.binder.names.length = left.binder.names.length := by
      rw [right.binder.arity, left.binder.arity, shape]
    .ok ⟨target, openChild left names.property.1.symm,
      openChild right (rightArity.trans names.property.1.symm)⟩
  else
    .error .rigidMismatch

private def rigidChildren (left right : Term scope) : Except PatternError (List Constraint) :=
  match left.view, right.view with
  | .node op terms children, .node op' terms' children' =>
    if equal : op = op' then by
      subst op'
      exact do
        let ordinary : List Constraint := (List.finRange (sig.terms op)).map fun i =>
          ⟨scope, terms i, terms' i⟩
        let underBinders ← (List.finRange (sig.scopes op)).mapM fun i =>
          alignChildren (children i) (children' i)
        pure (ordinary ++ underBinders)
    else .error .rigidMismatch
  | _, _ => .error .rigidMismatch

private def PatternApplication.bind (application : PatternApplication)
    (body : Term application.arguments) : MetaSubst :=
  let binder : Binder sig Nat := ⟨application.arguments.length, application.arguments, rfl⟩
  ⟨application.name, ⟨binder, application.distinct, body.sink (by simp [binder])⟩⟩

private def PatternApplication.project (application : PatternApplication) (fresh : String)
    (kept : List Nat) : MetaSubst :=
  let variables := application.arguments.attach.filterMap fun name =>
    if kept.contains name.val then some (AST.var name : Term application.arguments) else none
  let terms := variables.foldr Term.NamedTerms.cons Term.NamedTerms.nil
  application.bind (Term.NamedTerm.metavar fresh terms)

private inductive Assignment where
  | solve (replacement : MetaSubst)
  | prune (application : PatternApplication) (kept : List Nat)

private def chooseAssignment (application : PatternApplication) (right : Term scope) :
    Except PatternError Assignment := do
  -- Identical heads were already compared for equality. A repeated head can use
  -- only positions that supply the same variable on both sides.
  if let some other ← patternHead right then
    if other.name == application.name then
      let kept := (application.arguments.zip other.arguments).filterMap fun (left, right) =>
        if left == right then some left else none
      return .prune application kept
  let uses ← patternUses right.syntaxTree right.wellScoped []
  if uses.any (fun
      | .metavar other _ => other.name == application.name
      | .variable _ => false) then
    throw (.cyclic application.name)
  if let some body := right.restrict application.arguments then
    return .solve (application.bind body)
  for use in uses do
    if let .variable id := use then
      unless application.arguments.contains id do throw (.escapingVariable application.name id)
  for use in uses do
    if let .metavar other localNames := use then
      let kept := other.arguments.filter fun id =>
        localNames.contains id || application.arguments.contains id
      if kept.length < other.arguments.length then
        return .prune other kept
  throw .validationFailed

private def extendAssignments (substs : List MetaSubst) (assignment : MetaSubst) :
    Except PatternError (List MetaSubst) := do
  -- Simultaneous substitution inserts each body once, so update older bodies here.
  let earlier ← substs.mapM fun subst => do
    let body ← (applySubsts _ [assignment] subst.replacement.body).mapError .substitution
    pure { subst with replacement := { subst.replacement with body } }
  pure (assignment :: earlier)

private def solveWorklist (fuel : Nat) (pending : List Constraint) (substs : List MetaSubst)
    (next : Nat) : Except PatternError (List MetaSubst) :=
  match pending, fuel with
  | [], _ => pure substs
  | _ :: _, 0 => throw .fuelExhausted
  | equation :: remaining, fuel + 1 => do
    let left ← (applySubsts equation.scope substs equation.left).mapError .substitution
    let right ← (applySubsts equation.scope substs equation.right).mapError .substitution
    if matchTerms left right then
      solveWorklist fuel remaining substs next
    else
      let leftHead ← patternHead left
      let rightHead ← patternHead right
      let action ← match leftHead, rightHead with
        | some head, _ => some <$> chooseAssignment head right
        | none, some head => some <$> chooseAssignment head left
        | none, none => pure none
      match action with
      | none =>
        let children ← rigidChildren left right
        solveWorklist fuel (children ++ remaining) substs next
      | some (.solve assignment) =>
        solveWorklist fuel remaining (← extendAssignments substs assignment) next
      | some (.prune application kept) =>
        let assignment := application.project (freshPrefix ++ toString next) kept
        let substs ← extendAssignments substs assignment
        solveWorklist fuel (equation :: remaining) substs (next + 1)
termination_by structural fuel

/-- Unify SOAS equations whose metavariable arguments are distinct variables. Residual
metavariables represent shared parameters of flexible equations. Each worklist step consumes
one unit of fuel, including the recheck after an argument projection. -/
def solvePatterns (constraints : List Constraint) (fuel : Nat := 4096) :
    Except PatternError (PatternSolution constraints) := do
  let next ← validatePatterns constraints
  let substitutions ← solveWorklist fuel constraints [] next
  match checked : isSolutionFor substitutions constraints with
  | .ok true => pure ⟨substitutions, checked⟩
  | .ok false => throw .validationFailed
  | .error error => throw (.substitution error)

end FreeFoil.Examples.SOAS

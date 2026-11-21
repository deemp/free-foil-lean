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

end FreeFoil.Examples.SOAS

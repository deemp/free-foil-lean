import FreeFoil
import FreeFoil.Derive

namespace FreeFoil.Examples.LambdaPi

inductive Pattern where
  | wildcard | variable | pair (left right : Pattern)
  deriving DecidableEq

def Pattern.binders : Pattern → Nat
  | .wildcard => 0
  | .variable => 1
  | .pair left right => left.binders + right.binders

inductive NamedTerm where
  | var (name : String)
  | app (fn arg : NamedTerm)
  | lam (body : BoundSyntax Pattern Pattern.binders NamedTerm)
  | pi (domain : NamedTerm) (codomain : BoundSyntax Pattern Pattern.binders NamedTerm)
  | univ
  | pair (fst snd : NamedTerm)
  | first (term : NamedTerm)
  | second (term : NamedTerm)
  | product (fst snd : NamedTerm)

derive_free_foil NamedTerm with Pattern, Pattern.binders

namespace Raw

def wildcard : Binder sig String := ⟨.wildcard, [], rfl⟩

def varPattern (name : String) : Binder sig String := ⟨.variable, [name], rfl⟩

def pairPattern (left right : Binder sig String) : Binder sig String :=
  ⟨.pair left.shape right.shape, left.names ++ right.names, by
    simp [sig, Pattern.binders, left.arity, right.arity]⟩

def lamPattern (binder : Binder sig String) (body : Raw) : Raw :=
  lamScoped binder body

def lam (name : String) (body : Raw) : Raw :=
  lamPattern (varPattern name) body

def lamWildcard (body : Raw) : Raw :=
  lamPattern wildcard body

def piPattern (binder : Binder sig String) (domain codomain : Raw) : Raw :=
  piScoped domain binder codomain

def pi (name : String) (domain codomain : Raw) : Raw :=
  piPattern (varPattern name) domain codomain

end Raw

inductive EvalError where
  | outOfFuel
  deriving Repr

private def Pattern.arguments (shape : Pattern) (arg : Term scope) :
    Fin shape.binders → Term scope :=
  match shape with
  | .wildcard => Fin.elim0
  | .variable => fun _ => arg
  | .pair left right =>
    let fst := Term.first arg
    let snd := Term.second arg
    Fin.addCases (left.arguments fst) (right.arguments snd)

/-- Weak-head evaluation with a bound on recursive evaluation depth. -/
def whnf (scope : Scope) (fuel : Nat) (term : Term scope) : Except EvalError (Term scope) :=
  match fuel with
  | 0 => .error .outOfFuel
  | fuel + 1 =>
    match term.view with
    | .node .app terms _ => do
      let fn ← whnf scope fuel (terms 0)
      let arg := terms 1
      match fn.view with
      | .node .lam _ children =>
        let child := children 0
        let args i := child.binder.shape.arguments arg (Fin.cast child.binder.arity i)
        whnf scope fuel (child.instantiate scope .identity args)
      | _ => pure (Term.app fn arg)
    | .node .first terms _ => do
      let pair ← whnf scope fuel (terms 0)
      match pair.view with
      | .node .pair fields _ => whnf scope fuel (fields 0)
      | _ => pure (Term.first pair)
    | .node .second terms _ => do
      let pair ← whnf scope fuel (terms 0)
      match pair.view with
      | .node .pair fields _ => whnf scope fuel (fields 1)
      | _ => pure (Term.second pair)
    | _ => pure term

end FreeFoil.Examples.LambdaPi

import FreeFoil

namespace FreeFoil.Examples.LambdaPi

inductive Op where
  | app | lam | pi | univ | pair | first | second | product
  deriving DecidableEq

inductive Pattern where
  | wildcard | variable | pair (left right : Pattern)
  deriving DecidableEq

def Pattern.binders : Pattern → Nat
  | .wildcard => 0
  | .variable => 1
  | .pair left right => left.binders + right.binders

abbrev sig : Signature where
  Op := Op
  Pattern := Pattern
  terms
    | .app | .pair | .product => 2
    | .pi | .first | .second => 1
    | .lam | .univ => 0
  scopes
    | .lam | .pi => 1
    | _ => 0
  binders := Pattern.binders

abbrev Term := AST sig
abbrev Raw := Syntax sig String

namespace Raw

def var (name : String) : Raw := Syntax.var name

def app (fn arg : Raw) : Raw := .node .app (Fin.cases fn fun _ => arg) Fin.elim0 Fin.elim0

def wildcard : Binder sig String := ⟨.wildcard, [], rfl⟩

def varPattern (name : String) : Binder sig String := ⟨.variable, [name], rfl⟩

def pairPattern (left right : Binder sig String) : Binder sig String :=
  ⟨.pair left.shape right.shape, left.names ++ right.names, by
    simp [sig, Pattern.binders, left.arity, right.arity]⟩

def lamPattern (binder : Binder sig String) (body : Raw) : Raw :=
  .node .lam Fin.elim0 (fun _ => binder) (fun _ => body)

def lam (name : String) (body : Raw) : Raw :=
  lamPattern (varPattern name) body

def lamWildcard (body : Raw) : Raw :=
  lamPattern wildcard body

def piPattern (binder : Binder sig String) (domain codomain : Raw) : Raw :=
  .node .pi (fun _ => domain) (fun _ => binder) (fun _ => codomain)

def pi (name : String) (domain codomain : Raw) : Raw :=
  piPattern (varPattern name) domain codomain

def univ : Raw := .node .univ Fin.elim0 Fin.elim0 Fin.elim0

def pair (fst snd : Raw) : Raw := .node .pair (Fin.cases fst fun _ => snd) Fin.elim0 Fin.elim0

def first (term : Raw) : Raw := .node .first (fun _ => term) Fin.elim0 Fin.elim0

def second (term : Raw) : Raw := .node .second (fun _ => term) Fin.elim0 Fin.elim0

def product (fst snd : Raw) : Raw := .node .product (Fin.cases fst fun _ => snd) Fin.elim0 Fin.elim0

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
    let fst := AST.node (sig := sig) .first (fun _ => arg) Fin.elim0
    let snd := AST.node (sig := sig) .second (fun _ => arg) Fin.elim0
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
      | _ => pure (AST.node .app (Fin.cases fn fun _ => arg) Fin.elim0)
    | .node .first terms _ => do
      let pair ← whnf scope fuel (terms 0)
      match pair.view with
      | .node .pair fields _ => whnf scope fuel (fields 0)
      | _ => pure (AST.node .first (fun _ => pair) Fin.elim0)
    | .node .second terms _ => do
      let pair ← whnf scope fuel (terms 0)
      match pair.view with
      | .node .pair fields _ => whnf scope fuel (fields 1)
      | _ => pure (AST.node .second (fun _ => pair) Fin.elim0)
    | _ => pure term

end FreeFoil.Examples.LambdaPi

import FreeFoil

namespace FreeFoil.Examples.LambdaPi

inductive Op where
  | app | lam | pi | univ | pair | first | second | product
  deriving DecidableEq

inductive Pattern where
  | wildcard | variable
  deriving DecidableEq

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
  binders
    | .wildcard => 0
    | .variable => 1

abbrev Term := AST sig
abbrev Raw := Syntax sig String

namespace Raw

def var (name : String) : Raw := Syntax.var name

def app (fn arg : Raw) : Raw := .node .app (Fin.cases fn fun _ => arg) Fin.elim0 Fin.elim0

def lam (name : String) (body : Raw) : Raw :=
  .node .lam Fin.elim0 (fun _ => ⟨.variable, [name], rfl⟩) (fun _ => body)

def lamWildcard (body : Raw) : Raw :=
  .node .lam Fin.elim0 (fun _ => ⟨.wildcard, [], rfl⟩) (fun _ => body)

def pi (name : String) (domain codomain : Raw) : Raw :=
  .node .pi (fun _ => domain) (fun _ => ⟨.variable, [name], rfl⟩) (fun _ => codomain)

def univ : Raw := .node .univ Fin.elim0 Fin.elim0 Fin.elim0

def pair (fst snd : Raw) : Raw := .node .pair (Fin.cases fst fun _ => snd) Fin.elim0 Fin.elim0

def first (term : Raw) : Raw := .node .first (fun _ => term) Fin.elim0 Fin.elim0

def second (term : Raw) : Raw := .node .second (fun _ => term) Fin.elim0 Fin.elim0

def product (fst snd : Raw) : Raw := .node .product (Fin.cases fst fun _ => snd) Fin.elim0 Fin.elim0

end Raw

inductive EvalError where
  | outOfFuel
  deriving Repr

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
        whnf scope fuel ((children 0).instantiate scope .identity (fun _ => arg))
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

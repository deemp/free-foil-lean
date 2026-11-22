import FreeFoil
import FreeFoil.Derive

namespace FreeFoil.Examples.NbEDemos.Pairs

def arity (_ : Unit) : Nat := 2

inductive NamedTerm where
  | var (name : String)
  | pair (first second : NamedTerm)
  | first (pair : NamedTerm)
  | second (pair : NamedTerm)
  | split (pair : NamedTerm) (body : BoundSyntax Unit arity NamedTerm)

derive_free_foil NamedTerm with Unit, arity

private def reduceProjection (evaluator : NbE.Evaluator sig scope)
    (field : Fin 2) (arg : NbE.Thunk sig scope) : NbE.Result (Option (NbE.Value sig scope)) := do
  match ← evaluator.force arg with
  | .node .pair fields _ => some <$> evaluator.force (fields field)
  | _ => pure none

def nbeRules : NbE.Rules sig NbE.NoContext where
  reduce evaluator _ op terms children :=
    match op with
    | .first => reduceProjection evaluator 0 (terms 0)
    | .second => reduceProjection evaluator 1 (terms 0)
    | .split => do
      match ← evaluator.force (terms 0) with
      | .node .pair fields _ =>
        let body := children 0
        some <$> evaluator.instantiate body (fun i => fields (Fin.cast body.binder.arity i))
      | _ => pure none
    | _ => pure none
  extend _ _ _ _ _ _ := pure ()
  isHead op _ := match op with
    | .first | .second | .split => true
    | _ => false

end FreeFoil.Examples.NbEDemos.Pairs

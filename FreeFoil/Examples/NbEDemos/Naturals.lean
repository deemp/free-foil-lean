import FreeFoil
import FreeFoil.Derive

namespace FreeFoil.Examples.NbEDemos.Naturals

def arity (_ : Unit) : Nat := 2

inductive NamedTerm where
  | var (name : String)
  | zero
  | suc (pred : NamedTerm)
  | natrec (scrutinee base : NamedTerm) (step : BoundSyntax Unit arity NamedTerm)

derive_free_foil NamedTerm with Unit, arity

def nbeRules : NbE.Rules sig NbE.NoContext where
  reduce evaluator _ op terms children :=
    match op with
    | .natrec => evaluator.eliminate .natrec terms children 0 fun
      | .node .zero _ _ => some <$> evaluator.force (terms 1)
      | .node .suc args _ =>
        let pred := args 0
        let step := children 0
        -- The recursive call uses the same branches and is forced only if the step demands it.
        let recursive : NbE.Thunk sig _ := .node .natrec (Fin.cases pred fun _ => terms 1) children
        let bound : Fin 2 → NbE.Thunk sig _ := Fin.cases pred (fun _ => recursive)
        some <$> evaluator.instantiate step (fun i => bound (Fin.cast step.binder.arity i))
      | _ => pure none
    | _ => pure none
  extend _ _ _ _ _ _ := pure ()
  isHead op i := match op with
    | .natrec => i == 0
    | _ => false

end FreeFoil.Examples.NbEDemos.Naturals

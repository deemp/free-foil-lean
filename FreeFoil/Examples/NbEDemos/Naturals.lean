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

def fragment : NbE.Fragment sig where
  reduce position evaluator op terms children :=
    match op with
    | .natrec => position.eliminate evaluator .natrec terms children 0 fun value => do
      if (position.project .zero value).isSome then
        some <$> evaluator.force (terms 1)
      else if let some (args, _) := position.project .suc value then
        let pred := args 0
        -- Reuse both branches and suspend the recursive result.
        let recursive := position.node .natrec (Fin.cases pred fun _ => terms 1) children
        some <$> evaluator.instantiateAtArity (children 0) (Fin.cases pred fun _ : Fin 1 => recursive)
      else pure none
    | _ => pure none
  isHead op i := match op with
    | .natrec => i == 0
    | _ => false

def nbeRules : NbE.Rules sig NbE.NoContext := fragment.rules

end FreeFoil.Examples.NbEDemos.Naturals

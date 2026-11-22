import FreeFoil
import FreeFoil.Derive

namespace FreeFoil.Examples.NbEDemos.Booleans

def arity (_ : Unit) : Nat := 0

inductive NamedTerm where
  | var (name : String)
  | trueVal
  | falseVal
  | cond (condition thenBranch elseBranch : NamedTerm)

derive_free_foil NamedTerm with Unit, arity

def nbeRules : NbE.Rules sig NbE.NoContext where
  reduce evaluator _ op terms _ :=
    match op with
    | .cond => do
      match ← evaluator.force (terms 0) with
      | .node .trueVal _ _ => some <$> evaluator.force (terms 1)
      | .node .falseVal _ _ => some <$> evaluator.force (terms 2)
      | _ => pure none
    | _ => pure none
  extend _ _ _ _ _ _ := pure ()
  isHead op i := match op with
    | .cond => i == 0
    | _ => false

end FreeFoil.Examples.NbEDemos.Booleans

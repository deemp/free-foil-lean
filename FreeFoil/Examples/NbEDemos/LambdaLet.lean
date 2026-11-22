import FreeFoil
import FreeFoil.Derive

namespace FreeFoil.Examples.NbEDemos.LambdaLet

def arity (_ : Unit) : Nat := 1

inductive NamedTerm where
  | var (name : String)
  | app (fn arg : NamedTerm)
  | lam (body : BoundSyntax Unit arity NamedTerm)
  | letIn (value : NamedTerm) (body : BoundSyntax Unit arity NamedTerm)

derive_free_foil NamedTerm with Unit, arity

def nbeRules : NbE.Rules sig NbE.NoContext where
  reduce evaluator _ op terms children :=
    match op with
    | .app => evaluator.eliminate .app terms children 0 fun
      | .node .lam _ children => some <$> evaluator.instantiate (children 0) (fun _ => terms 1)
      | _ => pure none
    | .letIn => some <$> evaluator.instantiate (children 0) (fun _ => terms 0)
    | _ => pure none
  extend _ _ _ _ _ _ := pure ()
  isHead op i := match op with
    | .app => i == 0
    | _ => false

end FreeFoil.Examples.NbEDemos.LambdaLet

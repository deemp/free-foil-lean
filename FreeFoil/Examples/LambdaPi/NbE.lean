import FreeFoil.Examples.LambdaPi

namespace FreeFoil.Examples.LambdaPi

private def Pattern.delayedArguments (shape : Pattern) (arg : NbE.Thunk sig scope) :
    Fin shape.binders → NbE.Thunk sig scope :=
  match shape with
  | .wildcard => Fin.elim0
  | .variable => fun _ => arg
  | .pair left right =>
    let fst : NbE.Thunk sig scope := .node .first (fun _ => arg) Fin.elim0
    let snd : NbE.Thunk sig scope := .node .second (fun _ => arg) Fin.elim0
    Fin.addCases (left.delayedArguments fst) (right.delayedArguments snd)

private def reduceProjection (evaluator : NbE.Evaluator sig scope)
    (field : Fin 2) (arg : NbE.Thunk sig scope) : NbE.Result (Option (NbE.Value sig scope)) := do
  match ← evaluator.force arg with
  | .node .pair fields _ => some <$> evaluator.force (fields field)
  | _ => pure none

/-- The λΠ eliminations, including application to a recursive pair pattern. -/
def nbeRules : NbE.Rules sig NbE.NoContext where
  reduce evaluator _ op terms _ :=
    match op with
    | .app => do
      match ← evaluator.force (terms 0) with
      | .node .lam _ children =>
        let body := children 0
        let binder := body.binder
        let args i := binder.shape.delayedArguments (terms 1) (Fin.cast binder.arity i)
        some <$> evaluator.instantiate body args
      | _ => pure none
    | .first => reduceProjection evaluator 0 (terms 0)
    | .second => reduceProjection evaluator 1 (terms 0)
    | _ => pure none
  extend _ _ _ _ _ _ := pure ()
  isHead op i := match op with
    | .app => i == 0
    | .first | .second => true
    | _ => false

end FreeFoil.Examples.LambdaPi

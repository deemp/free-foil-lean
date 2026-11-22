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
    (field : Fin 2) (pair : NbE.Value sig scope) : NbE.Result (Option (NbE.Value sig scope)) :=
  match pair with
  | .node .pair fields _ => some <$> evaluator.force (fields field)
  | _ => pure none

/-- The λΠ eliminations, including application to a recursive pair pattern. -/
def nbeRules : NbE.Rules sig NbE.NoContext where
  reduce evaluator _ op terms children :=
    match op with
    | .app => evaluator.eliminate .app terms children 0 fun
      | .node .lam _ children =>
        let body := children 0
        let binder := body.binder
        let args i := binder.shape.delayedArguments (terms 1) (Fin.cast binder.arity i)
        some <$> evaluator.instantiate body args
      | _ => pure none
    | .first => evaluator.eliminate .first terms children 0 (reduceProjection evaluator 0)
    | .second => evaluator.eliminate .second terms children 0 (reduceProjection evaluator 1)
    | _ => pure none
  extend _ _ _ _ _ _ := pure ()
  isHead op i := match op with
    | .app => i == 0
    | .first | .second => true
    | _ => false
  eta op := match op with
    | .lam => some {
      term i _ _ := Fin.elim0 i
      body {scope} _ binder _ other := do
        if shape : binder.shape = .variable then
          have bound : 0 < binder.names.length := by
            rw [binder.arity, shape]
            decide
          let name : Name (binder.names ++ scope) :=
            ⟨binder.names[0], List.mem_append_left _ (List.getElem_mem bound)⟩
          some (.node .app (Fin.cases (.ready other) (fun _ => .var name)) Fin.elim0)
        else
          none }
    | _ => none

end FreeFoil.Examples.LambdaPi

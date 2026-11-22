import FreeFoil.NbE.Fragment

namespace FreeFoil.Examples.NbEDemos.Functions

inductive Op where
  | lam
  | app
  | pi
  deriving DecidableEq

abbrev sig : Signature where
  Op := Op
  Pattern := Unit
  terms
    | .lam => 0
    | .app => 2
    | .pi => 1
  scopes
    | .lam | .pi => 1
    | .app => 0
  binders _ := 1

def fragment : NbE.Fragment sig where
  reduce position evaluator op terms children :=
    match op with
    | .app => position.eliminate evaluator .app terms children 0 fun value => do
      let some (_, lambda) := position.project .lam value | return none
      some <$> evaluator.instantiateAtArity (lambda 0) (fun _ : Fin 1 => terms 1)
    | _ => pure none
  isHead op i := match op with
    | .app => i == 0
    | _ => false
  eta position op := match op with
    | .lam => some {
      term i _ _ := Fin.elim0 (Fin.cast (position.terms .lam) i)
      body {scope} _ binder _ other := do
        if arity : binder.names.length = 1 then
          have bound : 0 < binder.names.length := by rw [arity]; decide
          let name : Name (binder.names ++ scope) :=
            ⟨binder.names[0], List.mem_append_left _ (List.getElem_mem bound)⟩
          some (position.node .app (Fin.cases (.ready other) fun _ => .var name) Fin.elim0)
        else none }
    | _ => none

end FreeFoil.Examples.NbEDemos.Functions

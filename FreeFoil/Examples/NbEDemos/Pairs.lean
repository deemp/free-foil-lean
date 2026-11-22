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

private def reduceProjection [DecidableEq whole.Op] (position : sig.Embedding whole)
    (evaluator : NbE.Evaluator whole scope) (field : Fin 2) (pair : NbE.Value whole scope) :
    NbE.Result (Option (NbE.Value whole scope)) := do
  let some (fields, _) := position.project .pair pair | return none
  some <$> evaluator.force (fields field)

def fragment : NbE.Fragment sig where
  reduce position evaluator op terms children :=
    match op with
    | .first => position.eliminate evaluator .first terms children 0 (reduceProjection position evaluator 0)
    | .second => position.eliminate evaluator .second terms children 0 (reduceProjection position evaluator 1)
    | .split => position.eliminate evaluator .split terms children 0 fun value => do
      let some (fields, _) := position.project .pair value | return none
      some <$> evaluator.instantiateAtArity (children 0) fields
    | _ => pure none
  isHead op _ := match op with
    | .first | .second | .split => true
    | _ => false
  eta position op := match op with
    | .pair => some {
      term i _ other :=
        if (Fin.cast (position.terms .pair) i) == 0 then
          position.node .first (fun _ => .ready other) Fin.elim0
        else
          position.node .second (fun _ => .ready other) Fin.elim0
      body i _ _ _ := Fin.elim0 (Fin.cast (position.scopes .pair) i) }
    | _ => none

def nbeRules : NbE.Rules sig NbE.NoContext := fragment.rules

end FreeFoil.Examples.NbEDemos.Pairs

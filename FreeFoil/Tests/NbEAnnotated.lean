import FreeFoil.Examples.NbEDemos.Fragments
import FreeFoil.NbE.Annotated
import FreeFoil.NbE.Conversion

namespace FreeFoil.Tests.NbEAnnotated

open FreeFoil.Examples.NbEDemos

private abbrev Span := Nat × Nat
private abbrev Term := AnnotatedAST Fragments.sig Span

private def rules : NbE.Rules (Fragments.sig.annotated Span) NbE.NoContext :=
  (Fragments.fragment.annotated Span).rules

private def expectOk [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def parse (source : String) : IO (AST Fragments.sig []) := do
  let raw ← expectOk (Fragments.parse source)
  expectOk (AST.fromClosed raw)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def elimination : IO Unit := do
  let plain ← parse "fst ((\\x. (suc x, zero)) zero)"
  let .node (.inr (.inl .first)) terms _ := plain.view
    | throw (IO.userError "expected a projection")
  let principal : Term [] := (AnnotatedAST.ofAST (terms (0 : Fin 1))).annotate (4, 30)
  let projection : Term [] := AST.node (.original (.inr (.inl .first))) (fun _ => principal) Fin.elim0
  let term := AnnotatedAST.annotate projection (0, 30)
  let value ← expectOk (NbE.eval rules 128 () term)
  let .node (.original (.inr (.inr .suc))) _ _ := value
    | throw (IO.userError "the annotated projection did not produce a blank successor head")
  let normal ← expectOk (NbE.quote rules 128 () value)
  let erasedNormal ← expectOk (NbE.nf Fragments.nbeRules 128 () term.erase)
  check (AST.alphaEquiv normal (AnnotatedAST.ofAST erasedNormal))
    "full readback of the annotated projection disagreed with blank readback of the erased term"

private def annotateBody (plain payload : AST Fragments.sig []) (span : Span) : IO (Term []) := do
  let .node (.inl .lam) _ bodies := plain.view | throw (IO.userError "expected a lambda")
  let child := bodies (0 : Fin 1)
  let openPayload := AnnotatedAST.ofAST (payload.sink (by simp))
  let body := (AnnotatedAST.ofAST child.body).annotate span [AnnotatedAST.ofAST child.body, openPayload]
  return AST.node (.original (.inl .lam)) Fin.elim0 fun _ =>
    ⟨⟨child.binder.shape, child.binder.names, child.binder.arity⟩, child.distinct, body⟩

private def underBinder : IO Unit := do
  let span : Span := (4, 27)
  let plain ← parse "\\x. fst ((\\y. (y, zero)) x)"
  let omega ← parse "(\\y. y y) (\\y. y y)"
  let annotated ← annotateBody plain omega span
  let .node (.original (.inl .lam)) _ bodies := annotated.view
    | throw (IO.userError "expected an annotated lambda")
  let originalNames := (bodies (0 : Fin 1)).binder.names
  let term : Term originalNames := annotated.sink (by simp)
  let erased := AnnotatedAST.erase term

  let normal ← expectOk (NbE.nf rules 128 () term)
  let erasedNormal ← expectOk (NbE.nf Fragments.nbeRules 128 () erased)
  let identity ← parse "\\z. z"
  check (AST.alphaEquiv normal (AnnotatedAST.ofAST erasedNormal) &&
    (AnnotatedAST.erase normal).alphaEquiv (identity.sink (by simp)))
    "full readback changed an annotated body or kept its source annotations"

  let weak ← expectOk (NbE.whnf rules 128 () term)
  let erasedWeak ← expectOk (NbE.whnf Fragments.nbeRules 128 () erased)
  check ((AnnotatedAST.erase weak).alphaEquiv erasedWeak)
    "weak-head readback changed the erased frozen body"
  let .node (.original (.inl .lam)) _ bodies := weak.view
    | throw (IO.userError "weak-head readback changed the shape of the lambda")
  let frozen := bodies (0 : Fin 1)
  let some (storedSpan, payloads, subject) := AnnotatedAST.annotation? frozen.body
    | throw (IO.userError "weak-head readback dropped the frozen annotation")
  check (storedSpan == span && frozen.binder.names != originalNames &&
    subject.freeVars == frozen.binder.names &&
    payloads.map AST.freeVars == [frozen.binder.names, []])
    "weak-head readback lost the source span or did not freshen the frozen annotation terms"

  let zero ← parse "zero"
  let variant ← annotateBody plain zero (5, 31)
  check (← expectOk (NbE.convertible rules 128 () annotated variant))
    "conversion considered the source span or evaluated an annotation payload"
  let different ← annotateBody (← parse "\\x. zero") zero span
  check (!(← expectOk (NbE.convertible rules 128 () annotated different)))
    "conversion ignored a difference in the underlying syntax"

private def eta : IO Unit := do
  let left : Term [] := (AnnotatedAST.ofAST (← parse "\\p. (fst p, snd p)")).annotate (0, 18)
  let right : Term [] := (AnnotatedAST.ofAST (← parse "\\p. p")).annotate (0, 5)
  check (← expectOk (NbE.convertible rules 128 () left right))
    "the annotated rules did not preserve pair eta conversion"

def run : IO Unit := do
  elimination
  underBinder
  eta

end FreeFoil.Tests.NbEAnnotated

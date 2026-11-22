import FreeFoil.Examples.LambdaPi.NbE
import FreeFoil.Examples.LambdaPi.Program

namespace FreeFoil.Tests.NbE

open FreeFoil.Examples.LambdaPi

private def check (message : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError message)

private def expectOk [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def parse (source : String) : IO Raw :=
  match Parser.parseTerm source with
  | .ok term => pure term
  | .error error => throw (IO.userError s!"cannot parse {source}: {error}")

private def closed (source : String) : IO (Term []) := do
  expectOk (AST.fromClosed (← parse source))

private def normalizationTests : IO Unit := do
  let term ← closed "λ x. (λ y. y) x"
  let expected ← closed "λ x. x"
  let value ← expectOk (NbE.eval nbeRules 64 () term)
  let normal ← expectOk (NbE.quote nbeRules 64 () value)
  let weak ← expectOk (NbE.quoteWhnf nbeRules 64 () value)
  check "readback did not normalize under the lambda" (normal.alphaEquiv expected)
  check "weak readback reduced a redex in the lambda body" (weak.alphaEquiv term)

  let term ← closed "Π (x : (λ y. y) (𝕌)) → (λ z. z) x"
  let expectedNF ← closed "Π (x : 𝕌) → x"
  let expectedWhnf ← closed "Π (x : 𝕌) → (λ z. z) x"
  check "normalization missed a redex in a Pi"
    ((← expectOk (NbE.nf nbeRules 64 () term)).alphaEquiv expectedNF)
  check "WHNF did not distinguish ordinary and scoped Pi children"
    ((← expectOk (NbE.whnf nbeRules 64 () term)).alphaEquiv expectedWhnf)

  let term ← closed "(λ x. λ y. x) ((λ z. z) (𝕌))"
  let expected ← closed "λ y. 𝕌"
  check "weak readback did not reify a used captured argument"
    ((← expectOk (NbE.whnf nbeRules 64 () term)).alphaEquiv expected)

  let term ← closed "(λ (x, y). (y, x)) (((λ z. z) (𝕌), (𝕌, 𝕌)))"
  let expected ← closed "((𝕌, 𝕌), 𝕌)"
  check "instantiation changed the order of names in a pair pattern"
    ((← expectOk (NbE.nf nbeRules 64 () term)).alphaEquiv expected)

private def demandTests : IO Unit := do
  let omega := "(λ w. w w) (λ w. w w)"
  let diverging ← closed omega
  match NbE.nf nbeRules 32 () diverging with
  | .error .outOfFuel => pure ()
  | _ => throw (IO.userError "normalizing omega did not exhaust the budget")
  let term ← closed s!"(λ x. 𝕌) ({omega})"
  let expected ← closed "𝕌"
  check "normalization demanded an unused argument"
    ((← expectOk (NbE.nf nbeRules 32 () term)).alphaEquiv expected)
  let term ← closed s!"(λ (x, y). x) ((𝕌, {omega}))"
  check "normalization demanded an unused pattern component"
    ((← expectOk (NbE.nf nbeRules 32 () term)).alphaEquiv expected)
  let term ← closed s!"λ x. {omega}"
  check "WHNF demanded an unapplied body"
    ((← expectOk (NbE.whnf nbeRules 32 () term)).alphaEquiv term)
  match NbE.nf nbeRules 32 () term with
  | .error .outOfFuel => pure ()
  | _ => throw (IO.userError "full normalization ignored a diverging binder body")

private def openScope : Scope := [1]
private def global : Name openScope := ⟨1, by simp [openScope]⟩

private def openTerm (source : String) : IO (Term openScope) := do
  let raw ← parse source
  expectOk (AST.fromNamed openScope (fun name => if name == "g" then some global else none) raw)

private def openTests : IO Unit := do
  let term ← openTerm "π₁(g ((λ x. x) (𝕌)))"
  let expected ← openTerm "π₁(g (𝕌))"
  check "stuck eliminations did not retain their neutral head and normalize ordinary arguments"
    ((← expectOk (NbE.nf nbeRules 64 () term)).alphaEquiv expected)
  let fn ← closed "λ x. λ y. x"
  let term := Term.app (fn.sink (by simp)) (AST.var global)
  let expected ← openTerm "λ z. g"
  let weak ← expectOk (NbE.whnf nbeRules 64 () term)
  let normal ← expectOk (NbE.nf nbeRules 64 () term)
  check "full readback captured a free argument" (normal.alphaEquiv expected && normal.freeVars == [1])
  check "weak readback captured a free argument" (weak.alphaEquiv expected && weak.freeVars == [1])

  let term ← openTerm "g (𝕌)"
  let fn ← closed "λ x. x"
  let expected ← closed "𝕌"
  let value ← expectOk (NbE.evalUnder nbeRules 64 () (fun _ => .syntax fn (fun name =>
    nomatch name.property)) term)
  check "semantic substitution did not change the output scope"
    ((← expectOk (NbE.quote nbeRules 64 () value)).alphaEquiv expected)

private abbrev ClientContext (scope : Scope) := Nat × Name scope

private def contextualRules : NbE.Rules sig ClientContext where
  reduce evaluator _ := nbeRules.reduce evaluator ()
  extend _ ctx _ _ _ binder :=
    pure (ctx.1 + binder.names.length, ctx.2.sink (fun {_} mem => List.mem_append_right _ mem))
  refine _ ctx value :=
    match value with
    | .var name =>
      if ctx.1 == 2 && name == ctx.2 then pure (.node .univ Fin.elim0 Fin.elim0)
      else pure value
    | _ => pure value
  isHead := nbeRules.isHead

private def contextTests : IO Unit := do
  let term ← openTerm "λ x. λ y. (g, g y)"
  let expected ← openTerm "λ x. λ y. (𝕌, g y)"
  check "language-specific refinement missed context under binders or refined a principal head"
    ((← expectOk (NbE.nf contextualRules 64 (0, global) term)).alphaEquiv expected)
  check "weak readback refined a suspended scoped body"
    ((← expectOk (NbE.whnf contextualRules 64 (0, global) term)).alphaEquiv term)

def run : IO Unit := do
  normalizationTests
  demandTests
  openTests
  contextTests

end FreeFoil.Tests.NbE

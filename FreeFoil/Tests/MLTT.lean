import FreeFoil.Examples.MLTT

namespace FreeFoil.Tests.MLTT

open Examples.MLTT

private def verify (message : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError message)

private def expectOk [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def term (source : String) : IO (Term []) := do
  AST.fromClosed (← expectOk (Parser.parseTerm source)) |> expectOk

-- The examples here follow upstream Language.MLTT.ImplSpec at fdfbeef.
private def bidirectionalTests : IO Unit := do
  let ctx := Context.empty
  let polymorphic ← term "Π (A : 𝕌) → A → A"
  expectOk (check ctx 128 (← term "λ A x ⇒ x") polymorphic)
  let dependentPair ← term "Π (p : Σ (A : 𝕌) × A) → π₁ p"
  expectOk (check ctx 128 (← term "λ (A, x) ⇒ x") dependentPair)
  expectOk (check ctx 128 (← term "λ _ ⇒ tt") (← term "Π (A : 𝕌) → 𝟙"))
  let inferred ← expectOk (infer ctx 128 (← term "π₂ (𝟙, tt)"))
  verify "MLTT inferred the wrong type for the dependent projection"
    (inferred.alphaEquiv Term.unitType)
  let annotated ← term "(λ x ⇒ x : 𝟙 → 𝟙) tt"
  verify "MLTT could not infer the type of an ascribed lambda application"
    ((← expectOk (infer ctx 128 annotated)).alphaEquiv Term.unitType)

  let invalidArg ← term "(λ x ⇒ x : 𝟙 → 𝟙) 𝕌"
  verify "MLTT accepted an argument of the wrong type" (infer ctx 128 invalidArg).toOption.isNone
  let bareLambda ← term "λ x ⇒ x"
  verify "MLTT inferred a bare lambda" (infer ctx 128 bareLambda).toOption.isNone
  verify "MLTT checked a lambda against a non-Π type"
    (check ctx 128 bareLambda Term.unitType).toOption.isNone

  -- The upstream rule checks uses of a pattern by inserting its projections.
  let nonPairDomain ← term "𝟙 → 𝟙"
  expectOk (check ctx 128 (← term "λ (x, y) ⇒ tt") nonPairDomain)
  verify "MLTT accepted a projection from a non-Σ input"
    (check ctx 128 (← term "λ (x, y) ⇒ x") nonPairDomain).toOption.isNone
  let value ← term "let (x, _) = (tt, 𝟙) in x"
  verify "MLTT inferred the wrong type for a pattern let"
    ((← expectOk (infer ctx 128 value)).alphaEquiv Term.unitType)
  verify "MLTT failed to evaluate a pattern let"
    ((← expectOk (nf [] ctx.definitions 128 value)).alphaEquiv Term.unitVal)

private def conversionTests : IO Unit := do
  let agrees (lhs rhs : String) : IO Bool := do
    expectOk (conv [] Context.empty.definitions 128 (← term lhs) (← term rhs))
  verify "MLTT conversion missed beta reduction" (← agrees "(λ x ⇒ x) tt" "tt")
  verify "MLTT conversion compared binder names" (← agrees "λ x ⇒ x" "λ y ⇒ y")
  verify "MLTT conversion missed eta contraction" (← agrees "λ f ⇒ λ x ⇒ f x" "λ f ⇒ f")
  verify "MLTT conversion accepted unequal normal forms" (!(← agrees "λ x ⇒ x" "λ x ⇒ tt"))
  verify "MLTT conversion confused distinct pair-pattern bindings"
    (!(← agrees "λ (x, _) ⇒ x" "λ (_, y) ⇒ y"))
  let loop ← term "(λ x ⇒ x x) (λ x ⇒ x x)"
  match nf [] Context.empty.definitions 8 loop with
  | .error .outOfFuel => pure ()
  | .ok _ => throw (IO.userError "MLTT normalized a diverging term within its fuel budget")

private def contextTests : IO Unit := do
  let scope : Scope := [7, 11]
  let old : Name [11] := ⟨11, by decide⟩
  let x : Name scope := ⟨11, by decide⟩
  let assumption := Context.empty.extend 11 (by decide) Term.unitType
  let ctx : Context scope :=
    assumption.extend 7 (by decide) Term.unitType (some (Term.var old))
  let dependency : Name (11 :: scope) := ⟨7, by decide⟩
  let binding := Term.lam (variableBody 11 (Term.var dependency))
  let normal ← expectOk (nf scope ctx.definitions 128 binding)
  verify "MLTT unfolding below a sunk binder captured a free name" (normal.freeVars == [11])
  verify "MLTT lost the type of an explicitly allocated name"
    ((← expectOk (infer ctx 128 (Term.var x))).alphaEquiv Term.unitType)
  let etaBlocker ← term "λ x ⇒ x x"
  let inScope := etaBlocker.sink (by simp : [] ⊆ [0])
  let neutral := Context.empty.extend 0 (by decide) Term.unitType
  let normal ← expectOk (nf [0] neutral.definitions 128 inScope)
  verify "MLTT treated a shadowed ambient name as an eta contraction" (normal.alphaEquiv inScope)

private def programTests : IO Unit := do
  let source ← IO.FS.readFile "test/fixtures/mltt/core.mltt"
  let program ← expectOk (Parser.parseProgram source)
  verify "MLTT core fixture lost its module name" (program.moduleName == some "Core")
  let results ← expectOk ((runProgram program).mapM id)
  let definitions := results.filterMap fun
    | .defined name => some name
    | _ => none
  let checked := results.filter fun
    | .checked _ _ => true
    | _ => false
  let computed := results.filterMap fun
    | .computed result => some result
    | _ => none
  verify "MLTT core fixture lost a checked definition"
    (definitions == #["id", "compose", "snd", "transport"])
  verify "MLTT core fixture lost a check" (checked.size == 2)
  verify "MLTT core fixture reduced a command incorrectly" (computed == #["tt", "tt", "tt", "tt"])

  let source := "module Errors\n\
    def good : 𝟙 := tt\n\
    def good : 𝕌 := 𝕌\n\
    def bad : 𝟙 := 𝕌\n\
    compute bad\n\
    compute good"
  let results := runProgram (← expectOk (Parser.parseProgram source))
  match results with
  | #[.ok (.defined "good"), .error duplicate, .error _, .error unbound, .ok (.computed "tt")] =>
    verify "MLTT reported the wrong error for a duplicate definition" (duplicate.startsWith "duplicate")
    verify "MLTT installed an ill-typed definition" (unbound.startsWith "unbound")
  | _ => throw (IO.userError (reprStr results))

def run : IO Unit := do
  bidirectionalTests
  conversionTests
  contextTests
  programTests

end FreeFoil.Tests.MLTT

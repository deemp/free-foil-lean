import FreeFoil.Examples.NbEDemos.Program

namespace FreeFoil.Tests.NbEDefinitions

open FreeFoil.Examples FreeFoil.Examples.NbEDemos

private def expectOk [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def parseIn (demo : Demo sig) (scope : Scope) (labels : List String) (source : String) :
    IO (AST sig scope) := do
  let raw ← match demo.parse source with
    | .ok raw => pure raw
    | .error error => throw (IO.userError s!"cannot parse {source}: {error}")
  expectOk (AST.fromNamed scope (fun label => Name.ofId scope (labels.idxOf label)) raw)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checkReadback [DecidableEq sig.Op] [DecidableEq sig.Pattern]
    (demo : Demo sig) (defs : NbE.Definitions sig scope) (labels : List String)
    (cases : List (String × String × String)) : IO Unit := do
  let rules := demo.rules.withDefinitions
  let parse := parseIn demo scope labels
  for (source, expectedFolded, expectedUnfolded) in cases do
    let value ← expectOk (NbE.eval rules 128 ((), defs) (← parse source))
    let folded ← expectOk (NbE.quote rules 128 ((), defs.withUnfolding .folded) value)
    let unfolded ← expectOk (NbE.quote rules 128 ((), defs) value)
    check (folded.alphaEquiv (← parse expectedFolded)) s!"unexpected folded result for {source}"
    check (unfolded.alphaEquiv (← parse expectedUnfolded)) s!"unexpected unfolded result for {source}"
    let fromFolded ← expectOk (NbE.nf rules 128 ((), defs) folded)
    check (fromFolded.alphaEquiv unfolded) s!"unfolding the folded result changed {source}"

private def lambdaPiTests : IO Unit := do
  let labels := ["a", "b", "id", "alias", "p", "k", "omega", "fn"]
  let demo := { lambdaPi with parse := LambdaPi.Parser.parseTerm }
  let parse := parseIn demo
  let defs : NbE.Definitions LambdaPi.sig [0, 1] := .empty
  let defs := defs.define 2 (by decide) (← parse [0, 1] labels "λ x. x")
  let defs := defs.define 3 (by decide) (← parse [2, 0, 1] labels "id")
  let defs := defs.define 4 (by decide) (← parse [3, 2, 0, 1] labels "(alias, b)")
  let defs := defs.define 5 (by decide) (← parse [4, 3, 2, 0, 1] labels "λ x. λ y. x")
  let defs := defs.define 6 (by decide) (← parse [5, 4, 3, 2, 0, 1] labels "(λ w. w w) (λ w. w w)")
  let defs := defs.define 7 (by decide) (← parse [6, 5, 4, 3, 2, 0, 1] labels "λ x. alias x")
  checkReadback demo defs labels [
    ("a", "a", "a"),
    ("alias", "alias", "λ x. x"),
    ("alias a", "alias a", "a"),
    ("π₁(p)", "π₁(p)", "λ x. x"),
    ("π₁((alias, b))", "alias", "λ x. x"),
    ("λ alias. alias", "λ x. x", "λ x. x"),
    ("λ x. (alias x, π₂(p))", "λ x. (alias x, π₂(p))", "λ x. (x, b)"),
    ("a alias", "a alias", "a (λ x. x)")
  ]

  let rules := lambdaPi.rules.withDefinitions
  let parse := parse [7, 6, 5, 4, 3, 2, 0, 1] labels
  let ctx := ((), defs)
  let foldedCtx := ((), defs.withUnfolding .folded)
  let applied ← parse "alias a"
  let folded ← expectOk (NbE.whnf rules 128 foldedCtx applied)
  let unfolded ← expectOk (NbE.whnf rules 128 ctx applied)
  check (folded.alphaEquiv applied && unfolded.alphaEquiv (← parse "a"))
    "weak-head readback lost the choice of definition sides"
  let frozen ← expectOk (NbE.whnf rules 128 ctx (← parse "fn"))
  check (frozen.alphaEquiv (← parse "λ x. alias x")) "weak-head readback unfolded a frozen body"
  let divergent ← parse "a omega"
  check (← expectOk (NbE.convertible rules 128 ctx divergent divergent))
    "matching folded names forced a diverging definition"
  let divergent ← parse "omega a"
  check (← expectOk (NbE.convertible rules 128 ctx divergent divergent))
    "matching folded eliminations forced a diverging definition"
  for (left, right, expected) in [
    ("alias", "id", true),
    ("alias", "λ x. alias x", true),
    ("alias", "k", false),
    ("k a a", "k a b", true),
    ("k a a", "k b a", false),
    ("k a omega", "k a b", true),
    ("k a a", "a", true)
  ] do
    for ctx in [ctx, foldedCtx] do
      let actual ← expectOk (NbE.convertible rules 128 ctx (← parse left) (← parse right))
      check (actual == expected) s!"conversion returned {actual} for {left} and {right}"

private def demoEliminationTests : IO Unit := do
  let defs : NbE.Definitions Naturals.sig [] := .empty
  let defs := defs.define 0 (by decide) (← parseIn naturals [] [] "suc zero")
  let source := "natrec one { zero -> zero ; suc k, r -> suc r }"
  checkReadback naturals defs ["one"] [(source, source, "suc zero")]

  let defs : NbE.Definitions Booleans.sig [] := .empty
  let defs := defs.define 0 (by decide) (← parseIn booleans [] [] "true")
  let source := "if yes then false else true"
  checkReadback booleans defs ["yes"] [(source, source, "false")]

def run : IO Unit := do
  lambdaPiTests
  demoEliminationTests

end FreeFoil.Tests.NbEDefinitions

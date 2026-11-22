import FreeFoil.Examples.NbEDemos.Program

namespace FreeFoil.Tests.NbEConversion

open FreeFoil.Examples
open FreeFoil.Examples.NbEDemos

private def expectOk [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def parseIn (demo : Demo sig) (names : OpenNames) (source : String) :
    IO (AST sig names.scope) := do
  let raw ← match demo.parse source with
    | .ok raw => pure raw
    | .error error => throw (IO.userError s!"cannot parse {source}: {error}")
  expectOk (names.resolve raw)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checkCases [DecidableEq sig.Op] [DecidableEq sig.Pattern]
    (demo : Demo sig) (names : OpenNames) (cases : List (String × String × Bool)) : IO Unit := do
  for (before, after, expected) in cases do
    let left ← parseIn demo names before
    let right ← parseIn demo names after
    let actual ← expectOk (NbE.convertible demo.rules 64 () left right)
    check (actual == expected) s!"conversion returned {actual} for {before} and {after}"

private def checkEta [DecidableEq sig.Op] [DecidableEq sig.Pattern]
    (demo : Demo sig) (names : OpenNames) (expanded neutral : String) : IO Unit := do
  let left ← parseIn demo names expanded
  let right ← parseIn demo names neutral
  let withoutEta := { demo.rules with eta := fun _ => none }
  let leftValue ← expectOk (NbE.eval demo.rules 64 () left)
  let rightValue ← expectOk (NbE.eval demo.rules 64 () right)
  check (← expectOk (NbE.conv demo.rules 64 () leftValue rightValue))
    "direct value comparison missed η"
  check (← expectOk (NbE.conv demo.rules 64 () rightValue leftValue))
    "direct value comparison missed η in the opposite order"
  check (!(← expectOk (NbE.conv withoutEta 64 () leftValue rightValue)))
    "conversion used η when the language did not enable it"
  let leftNF ← expectOk (NbE.nf demo.rules 64 () left)
  let rightNF ← expectOk (NbE.nf demo.rules 64 () right)
  check (leftNF.alphaEquiv left && rightNF.alphaEquiv right && !leftNF.alphaEquiv rightNF)
    "ordinary normalization changed the η shape"

private def contextTests (names : OpenNames) : IO Unit := do
  let rules : NbE.Rules LambdaPi.sig (fun _ => Bool) := {
    reduce evaluator _ := lambdaPi.rules.reduce evaluator ()
    extend _ _ _ _ _ _ := pure true
    refine _ beneathBinder value :=
      match value with
      | .var _ =>
        if beneathBinder then pure (.node .univ Fin.elim0 Fin.elim0)
        else pure value
      | _ => pure value
    isHead := lambdaPi.rules.isHead
  }
  let left ← parseIn lambdaPi names "\\x. f"
  let right ← expectOk (names.resolve (LambdaPi.Raw.lam "z" LambdaPi.Raw.univ))
  check (← expectOk (NbE.convertible rules 64 false left right))
    "conversion did not use the context supplied under corresponding binders"
  let left ← parseIn lambdaPi names "\\x. f x"
  let right ← parseIn lambdaPi names "\\y. g y"
  check (!(← expectOk (NbE.convertible rules 64 false left right)))
    "refinement changed a principal head during conversion"

private def environmentTest (names : OpenNames) : IO Unit := do
  let openFn ← parseIn lambdaPi names "f"
  let identity ← expectOk (AST.fromClosed (LambdaPi.Raw.lam "x" (LambdaPi.Raw.var "x")))
  let renameToIdentity := fun _ => NbE.Thunk.syntax identity (fun name => nomatch name.property)
  check (← expectOk (NbE.convertibleUnder lambdaPi.rules 64 () renameToIdentity NbE.Thunk.var
      openFn identity))
    "conversion did not evaluate terms with different source scopes into their target scope"

def run : IO Unit := do
  let names ← expectOk (OpenNames.ofList ["f", "g"])
  let omega := "(\\w. w w) (\\w. w w)"
  checkCases lambdaPi names [
    ("\\x. (\\y. y) x", "\\z. z", true),
    ("(a : f) -> (\\b. b) a", "(u : f) -> u", true),
    ("\\x. \\y. x", "\\u. \\v. v", false),
    ("(x : f) -> x", "f", false),
    ("f", "g", false),
    (s!"f ({omega})", s!"g ({omega})", false),
    (s!"(x : f) -> {omega}", "f", false),
    ("\\x. f x x", "f", false),
    ("\\x. \\y. f x y", "f", true),
    ("f", "\\x. \\y. f x y", true)
  ]
  let divergence ← parseIn lambdaPi names s!"f ({omega})"
  match NbE.convertible lambdaPi.rules 32 () divergence divergence with
  | .error .outOfFuel => pure ()
  | _ => throw (IO.userError "conversion did not report fuel exhaustion for a demanded diverging child")
  checkEta lambdaPi names "\\x. f x" "f"
  contextTests names
  environmentTest names

  let names ← expectOk (OpenNames.ofList ["p", "q"])
  checkCases pairs names [
    ("fst (p, q)", "p", true),
    ("fst p", "snd p", false),
    ("split p as (x, y) in (y, x)", "split p as (a, b) in (b, a)", true),
    ("split p as (x, y) in x", "split p as (x, y) in y", false),
    ("(snd p, fst p)", "p", false),
    ("(fst p, snd p)", "q", false)
  ]
  checkEta pairs names "(fst p, snd p)" "p"

end FreeFoil.Tests.NbEConversion

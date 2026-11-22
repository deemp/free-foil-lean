import FreeFoil.Examples.LambdaPi.Program
import FreeFoil.Tests.Annotated
import FreeFoil.Tests.Derive
import FreeFoil.Tests.MLTT
import FreeFoil.Tests.MLTTCache
import FreeFoil.Tests.NbE
import FreeFoil.Tests.NbEDemos
import FreeFoil.Tests.SOAS
import FreeFoil.Tests.SubstitutionLaws

open FreeFoil
open FreeFoil.Examples.LambdaPi

example (x : Name []) : False := by
  have h := x.property
  simp at h

example (term : AST sig source) (h : source ⊆ target) :
    (term.sink h).syntaxTree = term.syntaxTree := rfl

private def check (message : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError message)

private def expectOk [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def closed (term : Raw) : IO (Term []) := expectOk (AST.fromClosed term)

private def alphaTests : IO Unit := do
  let shadowed ← closed (Raw.lam "x" (Raw.lam "x" (Raw.var "x")))
  let inner ← closed (Raw.lam "a" (Raw.lam "b" (Raw.var "b")))
  let outer ← closed (Raw.lam "a" (Raw.lam "b" (Raw.var "a")))
  check "renaming a shadowed binder changed alpha-equivalence" (shadowed.alphaEquiv inner)
  check "alpha-equivalence confused the inner and outer binders" (!shadowed.alphaEquiv outer)
  let universeTerm ← closed Raw.univ
  let pair ← closed (Raw.pair Raw.univ Raw.univ)
  let product ← closed (Raw.product Raw.univ Raw.univ)
  check "different operators were matched" (!pair.alphaEquiv product)
  let wildcard ← closed (Raw.lamWildcard Raw.univ)
  let namedBinder ← closed (Raw.lam "x" Raw.univ)
  check "different pattern shapes were matched" (!wildcard.alphaEquiv namedBinder)
  let hoisted := universeTerm.hoist (dst := sig) (fun shape => ⟨shape, rfl⟩) AST.node
  check "identity hoist changed the term" (hoisted.alphaEquiv universeTerm)

private def captureTest : IO Unit := do
  let fn ← closed (Raw.lam "x" (Raw.lam "y" (Raw.var "x")))
  let scope : Scope := [1]
  let y : Name scope := ⟨1, by simp [scope]⟩
  let fn := fn.sink (by simp)
  let term : Term scope := AST.node .app (Fin.cases fn fun _ => AST.var y) Fin.elim0
  let result ← expectOk (whnf scope 10 term)
  let resolve (name : String) := if name == "y" then some y else none
  let expected ← expectOk (AST.fromNamed scope resolve (Raw.lam "z" (Raw.var "y")))
  check "substitution captured the free argument" (result.alphaEquiv expected)
  check "substitution lost the free identifier" (result.freeVars == [1])
  check "restrict accepted a context missing a free name" (result.restrict []).isNone
  check "restrict rejected a context containing the support" (result.restrict [1]).isSome
  let normalized := AST.refresh scope result
  check "forced refresh changed the meaning of the term" (result.alphaEquiv normalized)

private def conversionTests : IO Unit := do
  let scope : Scope := [0]
  let x : Name scope := ⟨0, by simp [scope]⟩
  let resolve (name : String) := if name == "x1" then some x else none
  let raw := Raw.pi "y" (Raw.var "x1") (Raw.pair (Raw.var "y") (Raw.var "x1"))
  let term ← expectOk (AST.fromNamed scope resolve raw)
  let printed := AST.toNamed scope term (fun _ => "x1")
  let roundTrip ← expectOk (AST.fromNamed scope resolve printed)
  check "printing used a free name for a binder" (term.alphaEquiv roundTrip)
  let bad := Raw.pi "x" (Raw.var "x") (Raw.var "x")
  match AST.fromClosed bad with
  | .error (.unbound "x") => pure ()
  | _ => throw (IO.userError "the Pi binder was visible in its domain")

private def generatedSyntaxTests : IO Unit := do
  let binder x y :=
    Raw.pairPattern (Raw.varPattern x) (Raw.pairPattern Raw.wildcard (Raw.varPattern y))
  let pi domain x y :=
    NamedTerm.pi domain (BoundSyntax.ofBinder (binder x y) (.pair (.var x) (.var y)))
  match (pi .univ "x" "x").resolveClosed with
  | .error (.duplicateBinder ["x", "x"]) => pure ()
  | _ => throw (IO.userError "generated conversion accepted a duplicate pattern name")
  match (pi (.var "x") "x" "y").resolveClosed with
  | .error (.unbound "x") => pure ()
  | _ => throw (IO.userError "generated conversion made the Pi binder visible in its domain")
  let term ← expectOk ((pi .univ "x" "y").resolveClosed)
  let named := Term.toNamedTerm [] term (fun x => nomatch x.property)
  match named with
  | .pi .univ ⟨.pair .variable (.pair .wildcard .variable), [x, y], _, .pair (.var fst) (.var snd)⟩ =>
    check "generated reverse conversion reordered the pattern names" (x == fst && y == snd && x != y)
  | _ => throw (IO.userError "generated reverse conversion changed the Pi or its pattern")
  check "generated conversion changed the term up to alpha-equivalence"
    (term.alphaEquiv (← expectOk named.resolveClosed))

private abbrev pairSig : Signature where
  Op := Unit
  Pattern := Bool
  terms _ := 0
  scopes _ := 1
  binders _ := 2

private def bindsPair (shape : Bool) (x y used : String) : Syntax pairSig String :=
  .node () Fin.elim0 (fun _ => ⟨shape, [x, y], rfl⟩) (fun _ => .var used)

private def patternTests : IO Unit := do
  let pair ← expectOk (AST.fromClosed (bindsPair false "x" "y" "y"))
  let renamed ← expectOk (AST.fromClosed (bindsPair false "a" "b" "b"))
  let different ← expectOk (AST.fromClosed (bindsPair false "a" "b" "a"))
  let differentShape ← expectOk (AST.fromClosed (bindsPair true "a" "b" "b"))
  check "renaming a multi-name pattern changed its meaning" (pair.alphaEquiv renamed)
  check "pattern binding positions were ignored" (!pair.alphaEquiv different)
  check "pattern payloads were ignored" (!pair.alphaEquiv differentShape)
  match AST.fromClosed (bindsPair false "x" "x" "x") with
  | .error (.duplicateBinder _) => pure ()
  | _ => throw (IO.userError "duplicate pattern names were accepted")
  let invalid : Syntax pairSig Nat :=
    .node () Fin.elim0 (fun _ => ⟨false, [0, 0], rfl⟩) (fun _ => .var 0)
  check "numeric scope checking accepted a duplicate binder" (AST.ofSyntax [] invalid).isNone
  match pair.view with
  | .node _ _ children =>
    let child := children 0
    let result := child.instantiate [8, 9] (.weakening (by simp)) fun i =>
      if i.val == 0 then AST.var ⟨8, by simp⟩ else AST.var ⟨9, by simp⟩
    check "pattern arguments were substituted out of order" (result.freeVars == [9])
  | .var _ => throw (IO.userError "expected a scoped pattern")

private def telescopeTests : IO Unit := do
  let universeTerm ← closed Raw.univ
  let telescope : Telescope String Term [] [9, 6, 3] :=
    .cons "A" universeTerm 3 (by decide)
      (.cons "x" (AST.var ⟨3, by simp⟩) 6 (by decide)
        (.cons "B" (universeTerm.sink (by simp)) 9 (by decide) .nil))
  let term : Term [9, 6, 3] := AST.var ⟨6, by simp⟩
  check "telescope extension did not add each binder" (telescope.extendScope == [9, 6, 3])

  let renamed := telescope.rename [] id (fun renameName payload => payload.rename renameName)
  check "renaming did not change the telescope binder identifiers" (renamed.scope == [2, 1, 0])
  check "renaming changed dependent payloads up to alpha-equivalence"
    (telescope.alphaEquiv renamed.telescope)
  check "the lifted renaming did not move the term's reference"
    ((term.rename renamed.renameName).freeVars == [1])

  let some thinned := telescope.thin term | throw (IO.userError "dependent telescope thinning failed")
  check "thinning did not retain A and x and drop B" (thinned.scope == [6, 3])
  check "thinning changed the term's reference" (thinned.term.freeVars == [6])
  match thinned.scope, thinned.telescope with
  | _, .cons label domain a _ (.cons label' payload _ _ _) =>
    check "thinning changed the order of the telescope entries" (label == "A" && label' == "x")
    check "thinning changed a payload" (domain.alphaEquiv universeTerm && payload.freeVars == [a])
  | _, _ => throw (IO.userError "expected two retained entries")

  let relabelled : Telescope String Term [] [1, 0] :=
    .cons "T" universeTerm 0 (by decide) (.cons "y" (AST.var ⟨0, by simp⟩) 1 (by decide) .nil)
  let independent : Telescope String Term [] [1, 0] :=
    .cons "T" universeTerm 0 (by decide) (.cons "y" (universeTerm.sink (by simp)) 1 (by decide) .nil)
  check "alpha-equivalence considered entry labels" (thinned.telescope.alphaEquiv relabelled)
  check "alpha-equivalence ignored a dependent payload" (!thinned.telescope.alphaEquiv independent)
  check "alpha-equivalence ignored telescope length" (!thinned.telescope.alphaEquiv telescope)

private def openTelescopeTests : IO Unit := do
  let universeTerm ← closed Raw.univ
  let payload ← expectOk (AST.fromNamed [7, 8, 4] (fun name => match name with
    | "ambient" => some ⟨4, by simp⟩
    | "A" => some ⟨8, by simp⟩
    | _ => none) (Raw.lam "z" (Raw.pair (Raw.var "ambient") (Raw.var "A"))))
  let telescope : Telescope String Term [4] [5, 6, 7, 8, 4] :=
    .cons "A" (universeTerm.sink (by simp)) 8 (by decide)
      (.cons "unused" (universeTerm.sink (by simp)) 7 (by decide)
        (.cons "x" payload 6 (by decide)
          (.cons "y" (AST.var ⟨6, by simp⟩) 5 (by decide) .nil)))
  let term : Term [5, 6, 7, 8, 4] := AST.var ⟨5, by simp⟩
  let some thinned := telescope.thin term | throw (IO.userError "transitive telescope thinning failed")
  check "thinning lost a transitive dependency or retained the unused middle entry"
    (thinned.scope == [5, 6, 8, 4] && thinned.term.freeVars == [5])

  let ambient : Term [5, 6, 7, 8, 4] := AST.var ⟨4, by simp⟩
  let some thinned := telescope.thin ambient | throw (IO.userError "thinning to the ambient scope failed")
  check "thinning an ambient reference did not preserve the ambient scope"
    (thinned.scope == [4] && thinned.term.freeVars == [4])

  let renamed := telescope.rename [8] (fun _ => ⟨8, by simp⟩)
    (fun renameName payload => payload.rename renameName)
  let rec supports {outer inner : Scope} (entries : Telescope String Term outer inner) :
      List (List Nat) :=
    match entries with
    | .nil => []
    | .cons _ payload _ _ rest => payload.freeVars :: supports rest
  check "renaming captured a free name or lost a payload dependency"
    (supports renamed.telescope == [[], [], [8, 9], [11]])

private def evaluationTests : IO Unit := do
  let term ← closed (Raw.second (Raw.pair (Raw.lam "x" (Raw.var "x")) Raw.univ))
  let expected ← closed Raw.univ
  let result ← expectOk (whnf [] 10 term)
  check "projection failed to reduce" (result.alphaEquiv expected)
  let wildcard ← closed (Raw.app (Raw.lamWildcard Raw.univ) (Raw.lam "x" (Raw.var "x")))
  let result ← expectOk (whnf [] 10 wildcard)
  check "wildcard beta reduction failed" (result.alphaEquiv expected)
  let self := Raw.lam "x" (Raw.app (Raw.var "x") (Raw.var "x"))
  let omega ← closed (Raw.app self self)
  match whnf [] 8 omega with
  | .error .outOfFuel => pure ()
  | .ok _ => throw (IO.userError "a diverging term returned a weak-head normal form")

private def parseClosed (text : String) : IO (Term []) := do
  closed (← expectOk (Parser.parseTerm text))

private def lambdaPiPatternTests : IO Unit := do
  let term ← parseClosed "(λ (x, (_, y)). y x) ((λ a. a, (𝕌, λ b. b)))"
  let result ← expectOk (whnf [] 16 term)
  let identity ← parseClosed "λ a. a"
  check "nested pair binders lost binding order" (result.alphaEquiv identity)
  let wildcard ← parseClosed "(λ (_, _). 𝕌) ((λ x. x x) (λ x. x x))"
  let result ← expectOk (whnf [] 4 wildcard)
  check "an unused pair argument was evaluated" (result.alphaEquiv (← closed Raw.univ))

  let fn ← parseClosed "λ (x, _). λ y. x"
  let scope : Scope := [1]
  let y : Name scope := ⟨1, by simp [scope]⟩
  let arg : Term scope := AST.node .pair (fun _ => AST.var y) Fin.elim0
  let term : Term scope := AST.node .app (Fin.cases (fn.sink (by simp)) fun _ => arg) Fin.elim0
  let result ← expectOk (whnf scope 16 term)
  let expectedRaw ← expectOk (Parser.parseTerm "λ z. π₁((y, y))")
  let expected ← expectOk (AST.fromNamed scope (fun name => if name == "y" then some y else none) expectedRaw)
  check "pair substitution captured the free argument" (result.alphaEquiv expected && result.freeVars == [1])

  let duplicate ← expectOk (Parser.parseTerm "Π ((x, (_, x)) : 𝕌) → x")
  match AST.fromClosed duplicate with
  | .error (.duplicateBinder ["x", "x"]) => pure ()
  | _ => throw (IO.userError "a duplicate name in a nested Pi pattern was accepted")

private def lambdaPiProgramTests : IO Unit := do
  for text in [
    "Π ((a, (_, b)) : ((𝕌) × ((𝕌) × (𝕌)))) → λ _. (a, b)",
    "(λ x. x) ((𝕌, π₂((𝕌, 𝕌))))",
    "λ f. λ x. f (f x)",
    "λ f. λ x. f x × f x"
  ] do
    let before ← parseClosed text
    let after ← parseClosed (prettyTerm (before.toNamed [] fun x => nomatch x.property))
    check s!"parse and print round trip changed {text}" (before.alphaEquiv after)

  let program ← expectOk (Parser.parseProgram
    "-- a multiline command\ncompute\n  (λ (x, _). x) ((𝕌, 𝕌)) : 𝕌\n{- comment -}\ncheck 𝕌 : 𝕌;")
  check "program commands were lost" (program.size == 2)
  let some command := program[0]? | throw (IO.userError "program has no compute command")
  check "interpretation did not print weak-head normal form"
    ((interpret 16 command).toOption == some "𝕌")
  check "malformed patterns did not produce a parse error"
    (Parser.parseProgram "compute λ (x,). x : 𝕌").toOption.isNone
  check "unterminated comments did not produce a parse error"
    (Parser.parseProgram "{- comment").toOption.isNone
  let openTerm ← expectOk (Parser.parseTerm "missing")
  match interpret 16 (.compute openTerm Raw.univ) with
  | .error (.scope (.unbound "missing")) => pure ()
  | _ => throw (IO.userError "the interpreter did not report an unresolved free name")
  let divergent ← expectOk (Parser.parseTerm "(λ x. x x) (λ x. x x)")
  match interpret 8 (.compute divergent Raw.univ) with
  | .error (.evaluation .outOfFuel) => pure ()
  | _ => throw (IO.userError "the interpreter did not report evaluation fuel exhaustion")

def main : IO Unit := do
  alphaTests
  captureTest
  conversionTests
  generatedSyntaxTests
  patternTests
  telescopeTests
  openTelescopeTests
  evaluationTests
  lambdaPiPatternTests
  lambdaPiProgramTests
  FreeFoil.Tests.Annotated.run
  FreeFoil.Tests.Derive.run
  FreeFoil.Tests.SOAS.run
  FreeFoil.Tests.MLTT.run
  FreeFoil.Tests.MLTTCache.run
  FreeFoil.Tests.NbE.run
  FreeFoil.Tests.NbEDemos.run
  IO.println "Free Foil regression tests passed"

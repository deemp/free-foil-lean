import FreeFoil.Examples.NbEDemos.Program

namespace FreeFoil.Tests.NbEFragments

open FreeFoil.Examples.NbEDemos

private def expectOk [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def parse (language : Demo sig) (names : OpenNames) (source : String) :
    IO (AST sig names.scope) := do
  let raw ← expectOk (language.parse source)
  expectOk (names.resolve raw)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

-- These fixture terms and expected forms follow the pinned Test.Fragments examples.
private def normalForms (names : OpenNames) : IO Unit := do
  for (source, expected) in [
    ("(\\x. (x, x)) zero", "(zero, zero)"),
    ("fst ((\\x. (suc x, zero)) (suc (suc zero)))", "suc (suc (suc zero))"),
    ("natrec ((\\x. x) (suc (suc zero))) { zero -> suc (suc (suc zero)); suc (k, r) -> suc r }",
      "suc (suc (suc (suc (suc zero))))"),
    ("split (suc zero, suc (suc zero)) as (x, y) in natrec x { zero -> y; suc (k, r) -> suc r }",
      "suc (suc (suc zero))"),
    ("natrec (suc (suc zero)) { zero -> \\f. f; suc (k, r) -> (\\g. g) r }", "\\f. f"),
    ("fst (a zero)", "fst (a zero)"),
    ("split a as (x, y) in (\\z. z) x", "split a as (x, y) in x"),
    ("natrec a { zero -> (\\z. z) zero; suc (k, r) -> (\\z. z) r }",
      "natrec a { zero -> zero; suc (k, r) -> r }"),
    ("split (a, b) as (x, y) in (y, x)", "(b, a)"),
    ("(x : fst (zero, a)) -> (\\k. (x, k)) (suc zero)", "(y : zero) -> (y, suc zero)"),
    ("\\(x, y). x", "\\(x, y). x")
  ] do
    let flat ← parse monolith names source
    let composed ← parse fragments names source
    check ((Fragments.fromMonolith flat).alphaEquiv composed) s!"fragment parsing changed {source}"
    let flatNF ← expectOk (NbE.nf monolith.rules 128 () flat)
    let composedNF ← expectOk (NbE.nf fragments.rules 128 () composed)
    check ((Fragments.toMonolith composedNF).alphaEquiv flatNF)
      s!"flat and composed evaluation disagree on {source}"
    check (flatNF.alphaEquiv (← parse monolith names expected)) s!"unexpected normal form for {source}"
    let printed := fragments.pretty (composedNF.toNamed names.scope names.label)
    check (composedNF.alphaEquiv (← parse fragments names printed))
      s!"printing changed the composed normal form of {source}"

private def weakHeadForms (names : OpenNames) : IO Unit := do
  for (source, expected) in [
    ("split a as (x, y) in (\\z. z) x", "split a as (x, y) in (\\z. z) x"),
    ("natrec a { zero -> (\\z. z) zero; suc (k, r) -> (\\z. z) r }",
      "natrec a { zero -> zero; suc (k, r) -> (\\z. z) r }")
  ] do
    let flat ← expectOk (NbE.whnf monolith.rules 128 () (← parse monolith names source))
    let composed ← expectOk (NbE.whnf fragments.rules 128 () (← parse fragments names source))
    check ((Fragments.toMonolith composed).alphaEquiv flat &&
      flat.alphaEquiv (← parse monolith names expected)) s!"unexpected weak-head form for {source}"

private def conversion (names : OpenNames) : IO Unit := do
  for (left, right, expected) in [
    ("\\f. \\x. f x", "\\f. f", true),
    ("\\p. (fst p, snd p)", "\\p. p", true),
    ("\\f. \\x. (fst (f x), snd (f x))", "\\f. f", true),
    ("\\p. (fst p, fst p)", "\\p. p", false),
    ("\\n. natrec n { zero -> zero; suc (k, r) -> suc r }", "\\n. n", false),
    ("\\x. x", "\\(x, y). x", false)
  ] do
    let composed ← expectOk (NbE.convertible fragments.rules 128 ()
      (← parse fragments names left) (← parse fragments names right))
    let flat ← expectOk (NbE.convertible monolith.rules 128 ()
      (← parse monolith names left) (← parse monolith names right))
    check (composed == expected && flat == expected) s!"unexpected conversion of {left} and {right}"

private def definitions : IO Unit := do
  let defs : NbE.Definitions Fragments.sig [] := .empty
  let body ← parse fragments ⟨[], by decide⟩ "(\\x. (suc x, zero)) zero"
  let defs := defs.define 0 (by decide) body
  let names : OpenNames := ⟨["p"], by decide⟩
  let term ← parse fragments names "fst p"
  let rules := fragments.rules.withDefinitions
  let folded ← expectOk (NbE.nf rules 128 ((), defs.withUnfolding .folded) term)
  let unfolded ← expectOk (NbE.nf rules 128 ((), defs) term)
  check (folded.alphaEquiv term && unfolded.alphaEquiv (← parse fragments names "suc zero"))
    "a fragment projection did not preserve both sides of a defined principal"

def run : IO Unit := do
  let names ← expectOk (OpenNames.ofList ["a", "b"])
  normalForms names
  weakHeadForms names
  conversion names
  definitions
  let invalid ← parse fragments names "(\\(x, y). x) zero"
  match NbE.nf fragments.rules 128 () invalid with
  | .error (.invalidBinder 1 2) => pure ()
  | _ => throw (IO.userError "a lambda accepted the wrong number of pattern names")

end FreeFoil.Tests.NbEFragments

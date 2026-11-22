import FreeFoil.Examples.NbEDemos.Program

namespace FreeFoil.Tests.NbEDemos

open FreeFoil.Examples.NbEDemos

private def expectOk [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def checkCases {sig : Signature} [DecidableEq sig.Op] [DecidableEq sig.Pattern]
    (demo : Demo sig) (cases : List (List String × String × String)) : IO Unit := do
  for (names, source, expected) in cases do
    let context ← expectOk (OpenNames.ofList names)
    let parse input := (expectOk (demo.parse input)) >>= (expectOk ∘ context.resolve)
    let term ← parse source
    let printed := demo.pretty (term.toNamed context.scope context.label)
    unless term.alphaEquiv (← parse printed) do
      throw (IO.userError s!"printing changed {source} to {printed}")
    let normal ← expectOk (demo.normalize 1024 source names)
    unless (← parse normal).alphaEquiv (← parse expected) do
      throw (IO.userError s!"{source} normalized to {normal}, expected {expected}")

private def checkError (result : Except String String) (message : String) : IO Unit := do
  match result with
  | .error error =>
    unless error == message do
      throw (IO.userError s!"expected {message}, got {error}")
  | .ok output => throw (IO.userError s!"expected {message}, got {output}")

def run : IO Unit := do
  checkCases lambdaPi [
    ([], "(\\x. x) (\\y. y)", "\\y. y"),
    ([], "\\f. \\y. (\\x. x) (f y)", "\\f. \\y. f y"),
    ([], "(a : \\t. t) -> (\\y. y) a", "(a : \\t. t) -> a"),
    ([], "\\f. (a : f) -> (\\y. y) a", "\\f. (a : f) -> a"),
    (["f", "g"], "f ((\\x. x) g)", "f g"),
    (["a", "b"], "(\\x. a x) (b a)", "a (b a)"),
    (["f", "x2"], "(a : (\\z. z) f) -> (a x2)", "(b : f) -> b x2")
  ]
  checkCases booleans [
    ([], "if true then true else false", "true"),
    ([], "if false then true else false", "false"),
    ([], "if (if true then false else true) then true else false", "false"),
    (["x"], "if x then true else false", "if x then true else false"),
    (["x"], "if x then (if true then false else true) else false", "if x then false else false")
  ]
  checkCases lambdaLet [
    ([], "let id = \\x. x in id id", "\\x. x"),
    ([], "let x = \\a. a in let x = \\b. b b in x", "\\b. b b"),
    ([], "\\f. let y = f in y y", "\\f. f f"),
    ([], "let w = (\\x. x x) (\\x. x x) in \\y. y", "\\y. y"),
    (["f", "a"], "let z = (\\b. b) a in f z", "f a")
  ]
  -- The pinned pairs signature has no closed terms.
  checkCases pairs [
    (["a", "b", "c"], "fst (snd (a, (b, c)))", "b"),
    (["a", "b"], "(snd (a, b), fst (a, b))", "(b, a)"),
    (["a", "b"], "split (a, b) as (x, y) in (y, x)", "(b, a)"),
    (["a", "b"], "split (a, b) as (x, y) in split (y, x) as (x, y) in x", "b"),
    (["a"], "fst a", "fst a"),
    (["a"], "split a as (x, y) in (fst (y, x), x)", "split a as (u, v) in (v, u)"),
    (["a"], "fst (split a as (x, y) in (y, x))", "fst (split a as (u, v) in (v, u))")
  ]
  checkCases naturals [
    ([], "natrec zero { zero -> suc zero ; suc k, r -> r }", "suc zero"),
    ([], "natrec (suc (suc zero)) { zero -> suc (suc (suc zero)) ; suc k, r -> suc r }",
      "suc (suc (suc (suc (suc zero))))"),
    ([], "natrec (suc (suc (suc zero))) { zero -> zero ; suc k, r -> k }", "suc (suc zero)"),
    (["a"], "natrec a { zero -> zero ; suc k, r -> suc r }",
      "natrec a { zero -> zero ; suc p, q -> suc q }"),
    (["a", "b"], "natrec (suc a) { zero -> b ; suc k, r -> suc r }",
      "suc (natrec a { zero -> b ; suc p, q -> suc q })"),
    (["a"], "natrec (suc (suc a)) { zero -> zero ; suc k, r -> k }", "suc a"),
    (["a"], "natrec a { zero -> zero ; suc k, r -> natrec zero { zero -> r ; suc k', r' -> k' } }",
      "natrec a { zero -> zero ; suc p, q -> q }"),
    (["a", "b"],
      "natrec a { zero -> natrec (suc zero) { zero -> zero ; suc k, r -> b } ; suc k, r -> r }",
      "natrec a { zero -> b ; suc p, q -> q }")
  ]
  checkError (lambdaPi.normalize 1024 "(a : a) -> a") "unbound name 'a'"
  checkError (lambdaLet.normalize 1024 "let a = a in a") "unbound name 'a'"
  checkError (pairs.normalize 1024 "split a as (x,x) in x" ["a"]) "duplicate names in binder (x, x)"
  checkError (naturals.normalize 1024 "natrec zero { zero -> p; suc p, r -> zero }") "unbound name 'p'"
  checkError (naturals.normalize 1024 "natrec zero { zero -> zero; suc p, p -> p }")
    "duplicate names in binder (p, p)"
  checkError (booleans.normalize 1024 "x" ["x", "x"]) "free variable names must be distinct"

end FreeFoil.Tests.NbEDemos

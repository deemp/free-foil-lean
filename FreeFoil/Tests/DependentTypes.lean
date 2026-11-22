import FreeFoil.Alpha
import FreeFoil.Examples.DependentTypes.Program

namespace FreeFoil.Tests.DependentTypes

open FreeFoil.Examples.DependentTypes

private def fuel : Nat := 128

private def expectOk [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def checkThat (message : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- Closed examples from DependentTypes.Examples at the pinned upstream revision. -/
private def normalForms : IO Unit := do
  for (source, type, expected) in [
    ("\\(x : Unit). x", "(x : Unit) -> Unit", "\\(x : Unit). tt"),
    ("\\(f : (A : U 0) -> Unit). \\(A : U 0). f A",
      "(f : (A : U 0) -> Unit) -> (A : U 0) -> Unit",
      "\\(f : (A : U 0) -> Unit). \\(A : U 0). tt"),
    ("\\(A : U 0). \\(f : (x : A) -> A). f",
      "(A : U 0) -> (f : (x : A) -> A) -> (x : A) -> A",
      "\\(A : U 0). \\(f : (x : A) -> A). f"),
    ("\\(f : (x : Unit) -> Unit). f",
      "(f : (x : Unit) -> Unit) -> (x : Unit) -> Unit",
      "\\(f : (x : Unit) -> Unit). \\(x : Unit). tt"),
    ("\\(A : U 0). \\(p : (a : A) * ((\\(z : A). Unit) a)). second p",
      "(A : U 0) -> (p : (a : A) * ((\\(z : A). Unit) a)) -> Unit",
      "\\(A : U 0). \\(p : (a : A) * Unit). tt"),
    ("\\(A : U 0). \\(a : A). (\\(p : (x : A) * Unit). first p) (a, tt)",
      "(A : U 0) -> (a : A) -> A",
      "\\(A : U 0). \\(a : A). a"),
    ("\\(x : (\\(A : U 0). A) Unit). x", "(x : Unit) -> Unit", "\\(x : Unit). tt"),
    ("\\(A : U 0). A", "(A : U 0) -> U 1", "\\(A : U 0). A"),
    ("\\(f : (X : U 1) -> U 0). f",
      "(f : (X : U 1) -> U 0) -> (X : U 0) -> U 1",
      "\\(f : (X : U 1) -> U 0). f"),
    ("\\(p : (u : Unit) * Unit). p",
      "(p : (u : Unit) * Unit) -> (u : Unit) * Unit",
      "\\(p : (u : Unit) * Unit). (tt, tt)"),
    ("\\(A : U 0). \\(f : (x : Unit) -> A). \\(x : Unit). f x",
      "(A : U 0) -> (f : (x : Unit) -> A) -> (x : Unit) -> A",
      "\\(A : U 0). \\(f : (x : Unit) -> A). \\(x : Unit). f tt")
  ] do
    let (term, _) ← expectOk (elaborate fuel source type)
    let actual ← expectOk (nf .empty fuel term)
    let expected ← expectOk (parseClosed expected)
    checkThat s!"unexpected dependent normal form for {source}" (actual.erase.alphaEquiv expected)
  let source := "\\(x : Unit). x"
  let (term, _) ← expectOk (elaborate fuel source "(x : Unit) -> Unit")
  let weak ← expectOk (whnf .empty fuel term)
  let expected ← expectOk (parseClosed source)
  checkThat "weak-head readback entered a suspended body" (weak.erase.alphaEquiv expected)
  let shown ← expectOk (normalize fuel source "(x : Unit) -> Unit")
  checkThat "the named example did not print the normal form" (shown == "\\(x0 : Unit). tt")

private def conversions : IO Unit := do
  for (type, left, right, expected) in [
    ("(A : U 0) -> (f : (x : A) -> A) -> (x : A) -> A",
      "\\(A : U 0). \\(f : (x : A) -> A). f",
      "\\(A : U 0). \\(f : (x : A) -> A). \\(x : A). f x", true),
    ("(A : U 0) -> (B : (x : A) -> U 0) -> (p : (x : A) * B x) -> (x : A) * B x",
      "\\(A : U 0). \\(B : (x : A) -> U 0). \\(p : (x : A) * B x). p",
      "\\(A : U 0). \\(B : (x : A) -> U 0). \\(p : (x : A) * B x). (first p, second p)", true),
    ("(x : Unit) -> (y : Unit) -> Unit", "\\(x : Unit). \\(y : Unit). x",
      "\\(x : Unit). \\(y : Unit). y", true),
    ("(p : (u : Unit) * Unit) -> (q : (u : Unit) * Unit) -> (u : Unit) * Unit",
      "\\(p : (u : Unit) * Unit). \\(q : (u : Unit) * Unit). p",
      "\\(p : (u : Unit) * Unit). \\(q : (u : Unit) * Unit). q", true),
    ("(A : U 0) -> (f : (x : A) -> Unit) -> (g : (x : A) -> Unit) -> (x : A) -> Unit",
      "\\(A : U 0). (\\(B : (x : A) -> U 0). \\(f : (y : A) -> B y). \\(g : (y : A) -> B y). f) (\\(x : A). Unit)",
      "\\(A : U 0). (\\(B : (x : A) -> U 0). \\(f : (y : A) -> B y). \\(g : (y : A) -> B y). g) (\\(x : A). Unit)",
      true),
    ("(A : U 0) -> (x : A) -> (y : A) -> A",
      "\\(A : U 0). \\(x : A). \\(y : A). x",
      "\\(A : U 0). \\(x : A). \\(y : A). y", false),
    ("(A : U 0) -> (p : (x : A) * A) -> (x : A) * A",
      "\\(A : U 0). \\(p : (x : A) * A). p",
      "\\(A : U 0). \\(p : (x : A) * A). (second p, first p)", false)
  ] do
    let (left, _) ← expectOk (elaborate fuel left type)
    let (right, _) ← expectOk (elaborate fuel right type)
    let forward ← expectOk (convertible .empty fuel left right)
    let backward ← expectOk (convertible .empty fuel right left)
    checkThat s!"unexpected conversion at {type}" (forward == expected && backward == expected)

private def subtyping : IO Unit := do
  for (lower, upper, expected) in [
    ("U 0", "U 1", true),
    ("U 1", "U 0", false),
    ("(X : U 1) -> (x : X) -> X", "(X : U 0) -> (x : X) -> X", true),
    ("(X : U 0) * U 0", "(X : U 1) * U 1", true),
    ("(X : U 1) * U 0", "(X : U 0) * U 0", false),
    ("(F : (X : U 2) -> U 0) -> F (U 0)", "(F : (X : U 2) -> U 0) -> F (U 1)", false)
  ] do
    let (lowerTerm, _) ← expectOk (elaborate fuel lower "U 3")
    let (upperTerm, _) ← expectOk (elaborate fuel upper "U 3")
    let lowerValue ← expectOk (eval .empty fuel lowerTerm)
    let upperValue ← expectOk (eval .empty fuel upperTerm)
    let actual ← expectOk (isSubtype .empty fuel lowerValue upperValue)
    checkThat s!"unexpected subtyping result for {lower} and {upper}" (actual == expected)

private def rejections : IO Unit := do
  for (source, type) in [
    ("\\(x : Unit). x", "(x : U 0) -> U 0"),
    ("tt tt", "Unit"),
    ("\\(x : Unit). first x", "(x : Unit) -> Unit"),
    ("U 0", "U 0"),
    ("\\(A : U 1). A", "(A : U 1) -> U 0"),
    ("\\(f : (X : U 0) -> U 0). f", "(f : (X : U 0) -> U 0) -> (X : U 1) -> U 0")
  ] do
    let term ← expectOk (parseClosed source)
    let expected ← expectOk (parseClosed type)
    match elaborateScoped .empty fuel term expected with
    | .ok _ => throw (IO.userError s!"accepted ill-typed {source} at {type}")
    | .error .outOfFuel | .error (.evaluation _) =>
      throw (IO.userError s!"evaluation failed while checking {source} at {type}")
    | .error _ => pure ()

private def weakenedBinders : IO Unit := do
  let ctx : Typing [1, 0] :=
    (Typing.empty.assume [0] (universeValue 0)).assume [1] (.var ⟨0, by decide⟩)
  let raw (binder : Nat) : Surface.Term [1, 0] :=
    Surface.Term.lam Surface.Term.unitType ⟨⟨(), [binder], rfl⟩, by simp, .var ⟨1, by simp⟩⟩
  let (plain, type) ← expectOk (infer ctx fuel (raw 2))
  let (weakened, _) ← expectOk (infer ctx fuel (raw 0))
  let checked ← expectOk (check ctx fuel (raw 0) type)
  checkThat "elaboration captured a free name's type beneath a weakened binder"
    (weakened.alphaEquiv plain && checked.alphaEquiv plain)
  let normal ← expectOk (nf ctx fuel checked)
  for result in [checked, normal] do
    let .node .lam fields _ := result.view | throw (IO.userError "expected a lambda")
    checkThat "the lambda's type annotation lost its reference to the free type"
      ((fields 1).freeVars == [0])

def run : IO Unit := do
  normalForms
  conversions
  subtyping
  rejections
  weakenedBinders

end FreeFoil.Tests.DependentTypes

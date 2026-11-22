import FreeFoil.Examples.SOAS

namespace FreeFoil.Tests.SOAS

open Examples.SOAS

private def check (message : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError message)

private def expectOk [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def app (fn arg : NamedTerm) : NamedTerm :=
  NamedTerm.operator "App" [.plain fn, .plain arg]

private def lam (name : String) (body : NamedTerm) : NamedTerm :=
  NamedTerm.operator "Lam" [NamedArg.bind [name] body]

private def lam2 (first second : String) (body : NamedTerm) : NamedTerm :=
  NamedTerm.operator "Lam2" [NamedArg.bind [first, second] body]

private def zero : NamedTerm := NamedTerm.operator "Z" []

private abbrev mv := NamedTerm.metavariable

private def swap : IO MetaSubst :=
  expectOk (MetaSubst.fromNamed "?m" ["x", "y"] (app (.var "y") (.var "x")))

-- Transcribed from Language/SOAS/Impl.hs in upstream fdfbeef.
private def substitutionFixtures : IO Unit := do
  let expansion ← expectOk (MetaSubst.fromNamed "?m" ["x", "y"]
    (lam "z" (app (.var "z") (app (.var "x") (.var "y")))))
  let nested ← expectOk (NamedTerm.resolveClosed
    (lam "x" (mv "?m" [app (.var "x") (mv "?m" [.var "x", .var "x"]), .var "x"])))
  let inner := lam "c" (app (.var "c") (app (.var "a") (.var "a")))
  let argument := app (.var "a") inner
  let expected ← expectOk (NamedTerm.resolveClosed
    (lam "a" (lam "b" (app (.var "b") (app argument (.var "a"))))))
  let substituted ← expectOk (applySubsts [] [expansion] nested)
  check "SOAS nested substitution captured an argument" (matchTerms substituted expected)

  let swapEntry ← swap
  let original ← expectOk (NamedTerm.resolveClosed
    (lam "f" (lam "x" (mv "?m" [mv "?m" [.var "x", .var "f"], .var "f"]))))
  let expected ← expectOk (NamedTerm.resolveClosed
    (lam "f" (lam "x" (app (.var "f") (app (.var "f") (.var "x"))))))
  check "SOAS substitution changed argument order"
    (matchTerms (← expectOk (applySubsts [] [swapEntry] original)) expected)

  let first ← expectOk (MetaSubst.fromNamed "?m" ["x"] (mv "?n" [.var "x"]))
  let second ← expectOk (MetaSubst.fromNamed "?n" ["x"] zero)
  let original ← expectOk (NamedTerm.resolveClosed (mv "?m" [zero]))
  let expected ← expectOk (NamedTerm.resolveClosed (mv "?n" [zero]))
  check "SOAS substitution rewrote the replacement itself"
    (matchTerms (← expectOk (applySubsts [] [first, second] original)) expected)

  let wrongArity ← expectOk (NamedTerm.resolveClosed (mv "?m" []))
  match applySubsts [] [first] wrongArity with
  | .error (.arityMismatch "?m" 1 0) => pure ()
  | _ => throw (IO.userError "SOAS substitution accepted the wrong metavariable arity")

private def constraintFixtures : IO Unit := do
  let entry ← swap
  let nested := mv "?m" [mv "?m" [.var "x", .var "f"], .var "f"]
  let good ← expectOk (Constraint.fromNamed ["f", "x"]
    nested (app (.var "f") (app (.var "f") (.var "x"))))
  let bad ← expectOk (Constraint.fromNamed ["f", "x", "y"]
    nested (app (.var "f") (app (.var "f") (.var "y"))))
  check "SOAS rejected the upstream swap constraint" (← expectOk (isSolutionFor [entry] [good]))
  check "SOAS accepted the upstream mismatched-variable constraint"
    (!(← expectOk (isSolutionFor [entry] [good, bad])))

  let lamEntry ← expectOk (MetaSubst.fromNamed "?m" ["x"]
    (lam "f" (app (.var "f") (.var "x"))))
  let nested := mv "?m" [mv "?m" [.var "x"]]
  let good ← expectOk (Constraint.fromNamed ["x"] nested
    (lam "f" (app (.var "f") (lam "g" (app (.var "g") (.var "x"))))))
  let bad ← expectOk (Constraint.fromNamed ["y", "x"] nested
    (lam "f" (app (.var "f") (lam "g" (app (.var "g") (.var "y"))))))
  check "SOAS rejected the upstream nested-lambda constraint"
    (← expectOk (isSolutionFor [lamEntry] [good]))
  check "SOAS accepted a distinct free variable under nested lambdas"
    (!(← expectOk (isSolutionFor [lamEntry] [bad])))

  let paired ← expectOk (MetaSubst.fromNamed "?m" ["y"] (lam2 "a" "b" (.var "b")))
  let good ← expectOk (Constraint.fromNamed [] (mv "?m" [zero]) (lam2 "u" "v" (.var "v")))
  let bad ← expectOk (Constraint.fromNamed [] (mv "?m" [zero]) (lam2 "u" "v" (.var "u")))
  check "SOAS matching depended on binder identifiers instead of position"
    (← expectOk (isSolutionFor [paired] [good]))
  check "SOAS matching confused two binder positions"
    (!(← expectOk (isSolutionFor [paired] [bad])))

  let otherOperator ← expectOk (Constraint.fromNamed [] zero (NamedTerm.operator "Unit" []))
  let otherMetavariable ← expectOk (Constraint.fromNamed [] (mv "?a" []) (mv "?b" []))
  check "SOAS matching ignored the operator identifier"
    (!(← expectOk (isSolutionFor [] [otherOperator])))
  check "SOAS matching ignored the metavariable identifier"
    (!(← expectOk (isSolutionFor [] [otherMetavariable])))

private def unary (operator : String) (argument : NamedTerm) : NamedTerm :=
  NamedTerm.operator operator [.plain argument]

private def scopedLam (id : Nat) (body : Term (id :: scope)) : Term scope :=
  let binder : Binder sig Nat := ⟨1, [id], rfl⟩
  let scopedArg := Term.NamedArg.bound ⟨binder, by simp [binder], body⟩
  Term.NamedTerm.application "Lam" (Term.NamedArgs.cons scopedArg Term.NamedArgs.nil)

private def patternSolutions : IO Unit := do
  let x := NamedTerm.var "x"
  let y := NamedTerm.var "y"
  let z := NamedTerm.var "z"
  let unaryEquation ← expectOk (Constraint.fromNamed ["x"] (mv "?F" [x]) (unary "f" x))
  let unarySolution ← expectOk (solvePatterns [unaryEquation])
  let image ← expectOk (applySubsts unaryEquation.scope unarySolution.substitutions unaryEquation.left)
  check "SOAS did not solve the unary pattern equation" (matchTerms image unaryEquation.right)

  let first ← expectOk (Constraint.fromNamed ["x"] (mv "?F" [x]) (unary "f" (mv "?G" [x])))
  let underBinder ← expectOk (NamedTerm.resolve [4] (fun _ => some ⟨4, by simp⟩) (mv "?G" [x]))
  let second : Constraint := ⟨[], scopedLam 4 underBinder, scopedLam 7 (.var ⟨7, by simp⟩)⟩
  let composed ← expectOk (solvePatterns [first, second])
  check "SOAS failed to align renamed binders and compose its assignments"
    (← expectOk (isSolutionFor composed.substitutions [unaryEquation]))

  let flexFlex ← expectOk (Constraint.fromNamed ["x", "y", "z"]
    (mv "?F" [x, y]) (mv "?G" [y, z]))
  let specialize ← expectOk (Constraint.fromNamed ["y", "z"] (mv "?G" [y, z]) (unary "f" y))
  let freshNameCollision ← expectOk (Constraint.fromNamed [] (mv "?pattern0" []) zero)
  let shared ← expectOk (solvePatterns [flexFlex, specialize, freshNameCollision])
  let projected ← expectOk (Constraint.fromNamed ["x", "y"] (mv "?F" [x, y]) (unary "f" y))
  check "SOAS lost the shared parameter during flexible unification"
    (← expectOk (isSolutionFor shared.substitutions [projected]))

  let permutation ← expectOk (Constraint.fromNamed ["x", "y"] (mv "?F" [x, y]) (mv "?F" [y, x]))
  let projected ← expectOk (solvePatterns [permutation])
  check "SOAS left a permuted flexible head unsolved"
    (projected.substitutions.any (·.name == "?F"))

  let prune ← expectOk (Constraint.fromNamed ["x", "y"]
    (mv "?F" [x]) (lam "a" (mv "?H" [y, .var "a"])))
  let useLocal ← expectOk (Constraint.fromNamed ["y", "a"] (mv "?H" [y, .var "a"]) (unary "g" (.var "a")))
  let scopedSolution ← expectOk (solvePatterns [prune, useLocal])
  let expected ← expectOk (Constraint.fromNamed ["x"] (mv "?F" [x]) (lam "b" (unary "g" (.var "b"))))
  check "SOAS pruned a variable bound inside the assignment"
    (← expectOk (isSolutionFor scopedSolution.substitutions [expected]))

private def patternFailures : IO Unit := do
  let x := NamedTerm.var "x"
  let alias ← expectOk (Constraint.fromNamed ["x"] (mv "?F" [x]) (mv "?G" [x]))
  let cycle ← expectOk (Constraint.fromNamed ["x"] (mv "?G" [x]) (unary "f" (mv "?F" [x])))
  match solvePatterns [alias, cycle] with
  | .error (.cyclic "?G") => pure ()
  | _ => throw (IO.userError "SOAS accepted a cyclic assignment")

  let underBinder ← expectOk (NamedTerm.resolve [0, 0] (fun _ => some ⟨0, by simp⟩) (mv "?F" [x]))
  let capture : Constraint := ⟨[0], scopedLam 0 underBinder, scopedLam 7 (.var ⟨0, by simp⟩)⟩
  match solvePatterns [capture] with
  | .error (.escapingVariable "?F" 0) => pure ()
  | _ => throw (IO.userError "SOAS captured a free variable when aligning a shadowing binder")

  let mismatch ← expectOk (Constraint.fromNamed ["x"] (unary "f" x) (unary "g" x))
  match solvePatterns [mismatch] with
  | .error .rigidMismatch => pure ()
  | _ => throw (IO.userError "SOAS accepted a rigid mismatch")

  for arguments in [[unary "f" x], [x, x]] do
    let invalid := mv "?F" arguments
    let reflexive ← expectOk (Constraint.fromNamed ["x"] invalid invalid)
    match solvePatterns [reflexive] with
    | .error (.nonPattern "?F") => pure ()
    | _ => throw (IO.userError "SOAS did not distinguish an application outside the pattern fragment")

  let inconsistent ← expectOk (Constraint.fromNamed ["x"] (mv "?F" [x]) (mv "?F" []))
  match solvePatterns [inconsistent] with
  | .error (.arityMismatch "?F" 1 0) => pure ()
  | _ => throw (IO.userError "SOAS accepted inconsistent metavariable arities")

private def soasCodecs : IO Unit := do
  let source : NamedTyping :=
    .judgment (lam "x" (.var "x")) (.function (.var "a") (.product (.var "a") (.var "a")))
  let scope := [7]
  let resolve : String → Option (Name scope) :=
    fun name => if name == "a" then some ⟨7, by simp [scope]⟩ else none
  let term ← expectOk (NamedTyping.resolve scope resolve source)
  let some (.judgment subject (.function (.var "a") (.product (.var "a") (.var "a")))) :=
    Term.toNamedTyping scope term (fun _ => "a")
    | throw (IO.userError "SOAS generated typing conversion lost its term or type")
  let subject ← expectOk (NamedTerm.resolveClosed subject)
  let identity ← expectOk (NamedTerm.resolveClosed (lam "y" (.var "y")))
  check "SOAS generated typing conversion changed its scoped subject" (matchTerms subject identity)
  match NamedTerm.resolveClosed (lam2 "x" "x" (.var "x")) with
  | .error (.duplicateBinder ["x", "x"]) => pure ()
  | _ => throw (IO.userError "SOAS generated conversion accepted duplicate binders")

namespace MutualCodec

mutual
inductive SourceTerm where
  | var (name : String)
  | literal (label : String)
  | ascribed (term : SourceTerm) (type : SourceType)

inductive SourceType where
  | byTerm (term : BoundSyntax Nat bindingCount SourceTerm)
end

derive_free_foil [SourceTerm, SourceType] with Nat, bindingCount

def run : IO Unit := do
  let source := SourceTerm.ascribed (.literal "value") (.byTerm ⟨1, ["x"], rfl, .var "x"⟩)
  let checked ← expectOk (SourceTerm.resolveClosed source)
  let some (.ascribed (.literal "value") (.byTerm _)) :=
    Term.toSourceTerm [] checked (fun name => nomatch name.property)
    | throw (IO.userError "generated codecs did not preserve the recursive source categories")
  let some decoded := SourceTerm.fromRaw source.toRaw
    | throw (IO.userError "generated codec rejected its own encoding")
  let roundTrip ← expectOk (SourceTerm.resolveClosed decoded)
  check "generated mutual codec changed the binding structure" (checked.alphaEquiv roundTrip)
  let malformed := Raw.SourceTerm.ascribed (Raw.SourceTerm.literal "value")
    (Raw.SourceTerm.literal "not a type")
  check "generated mutual codec accepted a term in a type position"
    (SourceTerm.fromRaw malformed).isNone

end MutualCodec

def run : IO Unit := do
  substitutionFixtures
  constraintFixtures
  patternSolutions
  patternFailures
  soasCodecs
  MutualCodec.run

end FreeFoil.Tests.SOAS

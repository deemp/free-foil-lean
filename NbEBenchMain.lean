import FreeFoil.Benchmarks.NbEBaselines
import FreeFoil.Benchmarks.LambdaNWaysCorpus
import FreeFoil.Examples.NbEDemos.Program

open FreeFoil FreeFoil.Examples FreeFoil.Benchmarks.LambdaNWaysCorpus

private def fuel := 200000

private def nodes (term : AST sig scope) : Nat :=
  term.fold (Term := fun _ => Nat) (Child := fun _ => Nat)
    (fun _ => 1) (fun _ _ body => body) fun op terms children =>
      let ordinary := (List.finRange (sig.terms op)).foldl (fun n i => n + terms i) 1
      (List.finRange (sig.scopes op)).foldl (fun n i => n + children i) ordinary

private structure Column (canonical : Signature) (count : Nat) where
  label : String
  normalForm : Fin count → Except String (AST canonical [])
  normalSize : Fin count → Except String Nat

private def column (label : String) (input : Fin count → AST sig [])
    (normalize : AST sig [] → Except String (AST sig []))
    (toCanonical : AST sig [] → AST canonical []) : Column canonical count :=
  let normal i := normalize (input i)
  ⟨label, fun i => (normal i).map toCanonical, fun i => (normal i).map nodes⟩

private def checked (workload implementation : String) (i : Nat) (result : Except String α) :
    IO α :=
  IO.ofExcept (result.mapError fun error => s!"{workload} term {i + 1} ({implementation}): {error}")

private def verify [DecidableEq sig.Op] [DecidableEq sig.Pattern]
    (workload : String) (reference : Column sig count) (others : List (Column sig count)) :
    IO Nat := do
  let mut checksum := 0
  for i in List.finRange count do
    let expected ← checked workload reference.label i (reference.normalForm i)
    checksum := checksum + nodes expected
    for candidate in others do
      let actual ← checked workload candidate.label i (candidate.normalForm i)
      unless expected.alphaEquiv actual do
        throw (IO.userError
          s!"{workload} term {i.val + 1}: {reference.label} and {candidate.label} disagree")
  return checksum

@[noinline] private def sample (workload : String) (implementation : Column sig count) :
    IO (Nat × Nat) := do
  let positions := List.finRange count
  let start ← IO.monoNanosNow
  let mut checksum := 0
  for i in positions do
    checksum := checksum + (← checked workload implementation.label i (implementation.normalSize i))
  return ((← IO.monoNanosNow) - start, checksum)

private def run [DecidableEq sig.Op] [DecidableEq sig.Pattern] (samples : Nat)
    (workload : String) (reference : Column sig count) (others : List (Column sig count)) :
    IO Unit := do
  let checksum ← verify workload reference others
  IO.println s!"{workload}: α-equivalent on {count} term(s), {checksum} nodes in full normal forms"
  for implementation in reference :: others do
    let mut timings := []
    for _ in [:samples] do
      let (elapsed, actual) ← sample workload implementation
      unless actual == checksum do
        throw (IO.userError s!"{workload} ({implementation.label}): normal-form size changed")
      timings := elapsed :: timings
    let sorted := timings.mergeSort (· ≤ ·)
    let lo := sorted[(samples - 1) / 2]?.getD 0
    let hi := sorted[samples / 2]?.getD 0
    let median := (lo + hi) / 2
    IO.println s!"  {implementation.label}: {median} ns"

private def generic (rules : NbE.Rules sig NbE.NoContext) (term : AST sig []) :
    Except String (AST sig []) :=
  (NbE.nf rules fuel () term).mapError reprStr

private def runLambda (samples : Nat) (name : String) (inputs : Array (LambdaPi.Term []))
    (includeSubstitution : Bool) : IO Unit :=
  let input (i : Fin inputs.size) := inputs[i]
  let baseline := column "generic" input (generic LambdaPi.nbeRules) id
  let mono := column "monomorphic" input (Benchmarks.NbEBaselines.monomorphic fuel) id
  let subst := column "substitution" input (Benchmarks.NbEBaselines.substitution fuel) id
  run samples name baseline (mono :: if includeSubstitution then [subst] else [])

private def close (raw : Syntax sig String) : IO (AST sig []) :=
  IO.ofExcept ((AST.fromClosed raw).mapError reprStr)

private def identity : LambdaPi.Raw :=
  LambdaPi.Raw.lam "x" (.var "x")

private def church (n : Nat) : LambdaPi.Raw := Id.run do
  let mut body := LambdaPi.Raw.var "z"
  for _ in [:n] do
    body := .app (.var "s") body
  return LambdaPi.Raw.lam "s" (LambdaPi.Raw.lam "z" body)

private def nestedLets (depth : Nat) : LambdaPi.Raw :=
  if depth == 0 then identity
  else
    (List.range depth).foldr (fun i body =>
      let value := if i == 0 then identity else .var s!"x{i - 1}"
      LambdaPi.Raw.app (LambdaPi.Raw.lam s!"x{i}" body) value) (.var s!"x{depth - 1}")

private def nestedPi (depth : Nat) : LambdaPi.Raw :=
  (List.range depth).foldr (fun i body => LambdaPi.Raw.pi s!"x{i}" identity body) identity

private def nestedRedexes (depth : Nat) : LambdaPi.Raw :=
  (List.range depth).foldl (fun term _ => LambdaPi.Raw.app identity term) identity

private def runMixed (samples : Nat) : IO Unit := do
  let numeral (n : Nat) := (List.range n).foldl (fun term _ => s!"(suc {term})") "zero"
  let source :=
    s!"split ((\\x. x) {numeral 8}, {numeral 12}) as (m, n) in " ++
    "natrec m { zero -> zero; suc (k, r) -> " ++
    "natrec n { zero -> r; suc (i, acc) -> suc acc } }"
  let single ← close (← IO.ofExcept (NbEDemos.Monolith.parse source))
  let composed ← close (← IO.ofExcept (NbEDemos.Fragments.parse source))
  let flat := column "single signature" (fun _ : Fin 1 => single)
    (generic NbEDemos.Monolith.nbeRules) id
  let fragments := column "composed fragments" (fun _ : Fin 1 => composed)
    (generic NbEDemos.Fragments.nbeRules) NbEDemos.Fragments.toMonolith
  run samples "mixed multiplication 8 × 12" flat [fragments]

private def builtins (samples : Nat) : IO Unit := do
  for (name, raw) in [
    ("Church power 2^9", LambdaPi.Raw.app (church 9) (church 2)),
    ("nested identity redexes 256", nestedRedexes 256),
    ("nested lets 64", nestedLets 64),
    ("nested lets 256", nestedLets 256),
    ("nested Π binders 64", nestedPi 64),
    ("nested Π binders 256", nestedPi 256)
  ] do
    runLambda samples name #[← close raw] true
  runMixed samples

private structure Options where
  samples : Nat := 5
  corpus : Option System.FilePath := none

private def parseOptions (options : Options) : List String → Except String Options
  | [] => pure options
  | "--samples" :: raw :: rest =>
    match raw.toNat? with
    | some (n + 1) => parseOptions { options with samples := n + 1 } rest
    | _ => throw "--samples expects a positive integer"
  | "--corpus" :: dir :: rest => parseOptions { options with corpus := some ⟨dir⟩ } rest
  | _ => throw "usage: lake exe nbeBench [--samples N] [--corpus LAMS_DIR]"

def main (args : List String) : IO Unit := do
  let options ← IO.ofExcept (parseOptions {} args)
  IO.println s!"Median of {options.samples} samples per implementation"
  builtins options.samples
  if let some dir := options.corpus then
    let factorial ← IO.ofExcept (← readTerm (dir / "lennart.lam")).close
    runLambda options.samples "factorial" #[factorial] false
    for name in ["random15", "random20"] do
      let inputs ← (← readGroup (dir / (name ++ ".lam"))).mapM fun input =>
        IO.ofExcept input.close
      runLambda options.samples name inputs false

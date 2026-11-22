import FreeFoil.Benchmarks.LambdaNWaysCorpus
import FreeFoil.Benchmarks.NbEBaselines

open FreeFoil FreeFoil.Examples.LambdaPi FreeFoil.Benchmarks.LambdaNWaysCorpus

private def fuel := 200000

private def nodes (term : Term scope) : Nat :=
  term.fold (Term := fun _ => Nat) (Child := fun _ => Nat)
    (fun _ => 1) (fun _ _ body => body) fun _ terms children =>
      1 + (List.ofFn terms).sum + (List.ofFn children).sum

private structure Reference where
  location : String
  input : Term []
  expected : Term []

private def prepare (input expected : Fixture) : IO Reference := do
  return ⟨input.location, ← IO.ofExcept input.close, ← IO.ofExcept expected.close⟩

private def readReferences (dir : System.FilePath) (group : String) : IO (Array Reference) := do
  let inputs ← readGroup (dir / (group ++ ".lam"))
  let expected ← readGroup (dir / (group ++ ".nf.lam"))
  unless inputs.size == expected.size do
    throw (IO.userError s!"{group}: {inputs.size} inputs but {expected.size} reference forms")
  (inputs.zip expected).mapM fun (input, normal) => prepare input normal

private def normalize (references : Array Reference) : Except String Unit := do
  for reference in references do
    let result ← (Benchmarks.NbEBaselines.substitution fuel reference.input).mapError fun error =>
      s!"{reference.location}: {error}"
    unless result.alphaEquiv reference.expected do
      throw s!"{reference.location}: normal form disagrees with the upstream reference"

@[noinline] private def sample (work : Unit → Except String Unit) : IO Nat := do
  let start ← IO.monoNanosNow
  IO.ofExcept (work ())
  return (← IO.monoNanosNow) - start

private def run (samples : Nat) (group details : String) (work : Unit → Except String Unit) :
    IO Unit := do
  let mut timings := #[]
  for _ in [:samples] do
    timings := timings.push (← sample work)
  let sorted := timings.qsort (· ≤ ·)
  let median := (sorted[(samples - 1) / 2]! + sorted[samples / 2]!) / 2
  IO.println s!"{group}: {median} ns ({details})"

private def compare (group : String) (left right : Term []) : Except String Unit :=
  unless left.alphaEquiv right do
    throw s!"{group}: Lennart terms are not α-equivalent"

private structure Options where
  samples : Nat := 5
  corpus : System.FilePath := "free-foil-repos/lambda-n-ways/lams"

private def parseOptions (options : Options) : List String → Except String Options
  | [] => pure options
  | "--samples" :: raw :: rest =>
    match raw.toNat? with
    | some (n + 1) => parseOptions { options with samples := n + 1 } rest
    | _ => throw "--samples expects a positive integer"
  | "--corpus" :: dir :: rest => parseOptions { options with corpus := ⟨dir⟩ } rest
  | _ => throw "usage: lake exe lambdaNWaysBench [--samples N] [--corpus LAMS_DIR]"

def main (args : List String) : IO Unit := do
  let options ← IO.ofExcept (parseOptions {} args)
  let random15 ← readReferences options.corpus "random15"
  let random20 ← readReferences options.corpus "random20"
  let lennart ← readTerm (options.corpus / "lennart.lam")
  let expected ← readTerm (options.corpus / "lennart.nf.lam")
  let factorial ← prepare lennart expected
  let size := nodes factorial.input
  -- Scope checking the shifted syntax is part of setup for the freshened comparison.
  let some fresh := AST.ofSyntax [] (factorial.input.syntaxTree.mapNames (· + 1))
    | throw (IO.userError "aeq: freshened Lennart term failed scope checking")

  IO.println s!"Median of {options.samples} sample(s) per workload"
  for (name, references) in [("random15", random15), ("random20", random20)] do
    run options.samples name s!"{references.size} reference normal forms matched" fun () =>
      normalize references
  run options.samples "conv" s!"{size} converted nodes" fun () => do
    unless nodes (← lennart.close) == size do
      throw "conv: converted node count changed"
  run options.samples "nf" "Lennart reference normal form matched" fun () => normalize #[factorial]
  run options.samples "aeq" "freshened Lennart term is α-equivalent" fun () =>
    compare "aeq" factorial.input fresh
  run options.samples "aeqs" "Lennart term is α-equivalent to itself" fun () =>
    compare "aeqs" factorial.input factorial.input

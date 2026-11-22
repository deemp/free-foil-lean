# Free Foil for Lean 4

Free Foil provides scope-safe syntax and capture-avoiding substitution for languages with binders. Define a signature for your language and reuse substitution, α-equivalence, scope restriction, and conversion between named and scope-checked syntax. The port follows the [Free Foil paper](https://arxiv.org/abs/2405.16384) and the [upstream Haskell implementation at `fdfbeef`](https://github.com/fizruk/free-foil/tree/fdfbeef).

## Build and test

Use the Lean version in `lean-toolchain`. The repository's Nix development shell also provides Lean and Lake. The library has no external Lean dependencies.

```sh
lake build
lake test
```

## Try the λΠ example

```lean
import FreeFoil.Examples.LambdaPi

open FreeFoil FreeFoil.Examples.LambdaPi

-- (λx. x) applied to the universe reduces to the universe.
#eval (do
  let term ← (AST.fromClosed (Raw.app (Raw.lam "x" (Raw.var "x")) Raw.univ)).toOption
  let result ← (whnf [] 16 term).toOption
  let expected ← (AST.fromClosed Raw.univ).toOption
  pure (result.alphaEquiv expected) : Option Bool)
-- some true
```

The example also supports dependent function types, recursive pair patterns, wildcard binders, pairs, and projections. Its evaluator reports fuel exhaustion on inputs that do not reach a weak-head normal form within the evaluation budget.

Run an upstream-style λΠ program with `lake exe lambdaPi program.lp`, or send it to standard input.

```sh
printf '%s\n' 'compute (λ (x, _). x) ((𝕌, 𝕌)) : 𝕌;' | lake exe lambdaPi
```

The example prints `𝕌`. The interpreter evaluates each closed `compute` term to weak-head normal form. It parses type annotations and reports `check` commands as unimplemented.

## Normalize by evaluation

`FreeFoil.NbE` evaluates scope-checked syntax to semantic values with suspended children. A language supplies a `NbE.Rules` record whose elimination rules demand the arguments they need and instantiate scoped children in binding order. Free names start as neutral values. Use `NbE.NoContext` for scope-only evaluation, or supply a scope-indexed context and describe how it extends under a binder.

`NbE.eval` and `NbE.quote` expose the two stages separately. `NbE.nf` runs both and normalizes under binders. `NbE.whnf` reads back ordinary arguments and leaves the head's scoped bodies unevaluated. Both take a recursion budget and can return `.outOfFuel`. Languages can supply a readback refinement rule for features such as type-directed η expansion. The λΠ rules below perform β-reduction and pair elimination.

```lean
import FreeFoil.Examples.LambdaPi.NbE
import FreeFoil.Examples.LambdaPi.Program

open FreeFoil FreeFoil.Examples.LambdaPi

#eval (do
  let raw ← (Parser.parseTerm "λ x. (λ y. y) x").toOption
  let term ← (AST.fromClosed raw).toOption
  let weak ← (NbE.whnf nbeRules 64 () term).toOption
  let full ← (NbE.nf nbeRules 64 () term).toOption
  let showTerm (t : Term []) := prettyTerm (t.toNamed [] fun name => nomatch name.property)
  pure (showTerm weak, showTerm full) : Option (String × String))
-- some ("λ x0. (λ x1. x1) x0", "λ x0. x0")
```

`NbE.conv` compares semantic values directly. Use `NbE.convertible` for
scope-checked terms and `NbE.convertibleUnder` for terms with separate semantic
environments. Matching heads compare children on demand without reading back
the values. Languages can enable η comparison by supplying observers for
introduction forms. The λΠ demo observes a function by applying it to a fresh
variable, and the pairs demo observes a pair with its projections. Ordinary
normalization preserves these introduction forms.

```lean
import FreeFoil.Examples.NbEDemos.Program

open FreeFoil FreeFoil.Examples.NbEDemos

#eval (do
  let names ← (OpenNames.ofList ["f"]).toOption
  let resolve source := do
    let raw ← (lambdaPi.parse source).toOption
    (names.resolve raw).toOption
  let expanded ← resolve "\\x. f x"
  let neutral ← resolve "f"
  (NbE.convertible lambdaPi.rules 64 () expanded neutral).toOption : Option Bool)
-- some true
```

The `nbe` executable reads one named term and prints its full normal form. Supply
any free variable names after the term. The λΠ, lambda-let, pairs, and naturals
commands use the syntax from the pinned `free-foil-NBE` demos.

```sh
lake exe nbe lambda-pi '(a : \t. t) -> (\y. y) a'
lake exe nbe booleans 'if true then false else true'
lake exe nbe let 'let id = \x. x in id id'
lake exe nbe pairs 'split (a, b) as (x, y) in (y, x)' a b
lake exe nbe naturals 'natrec (suc a) { zero -> zero; suc p, r -> suc r }' a
```

The pairs example prints `(b, a)`. The naturals example unfolds once and leaves
a recursion on the free variable `a`. Bound names in the output are generated
by scope-safe readback.

### Normalize with named definitions

Wrap a language's rules with `Rules.withDefinitions` and pass the definition
table alongside its usual context. Each `Definitions.define` introduces a fresh
identifier whose body is scoped over the preceding entries. Undefined names
remain neutral. A language rule uses `Evaluator.eliminate` to match a principal
operand when reduction may need to look through a definition.

Readback unfolds definitions by default. Use `withUnfolding .folded` to retain
their names, including at the head of eliminations. Conversion tries matching
folded heads before demanding their bodies, regardless of the readback choice.

```lean
import FreeFoil.Examples.LambdaPi.NbE
import FreeFoil.Examples.LambdaPi.Program

open FreeFoil FreeFoil.Examples.LambdaPi

#eval (do
  let identity ← (AST.fromClosed (Raw.lam "x" (Raw.var "x"))).toOption
  let defs : NbE.Definitions sig [] := .empty
  let defs := defs.define 0 (by decide) identity
  let defs := defs.define 1 (by decide) (AST.var ⟨0, by decide⟩)
  let raw := Raw.lam "x" (Raw.app (Raw.var "alias") (Raw.var "x"))
  let term ← (AST.fromNamed [1, 0]
    (fun name => if name == "alias" then some ⟨1, by decide⟩ else none) raw).toOption
  let rules := nbeRules.withDefinitions
  let value ← (NbE.eval rules 64 ((), defs) term).toOption
  let folded ← (NbE.quote rules 64 ((), defs.withUnfolding .folded) value).toOption
  let unfolded ← (NbE.quote rules 64 ((), defs) value).toOption
  let showTerm (t : Term [1, 0]) :=
    prettyTerm (t.toNamed [1, 0] fun name => if name.id == 0 then "id" else "alias")
  pure (showTerm folded, showTerm unfolded) : Option (String × String))
-- some ("λ x2. alias x2", "λ x2. x2")
```

### Compose normalization rules

The `fragments` demo combines functions, pairs, and naturals in the pinned
monolith syntax. This term applies a function inside a projection and then
recurses on the resulting numeral. It prints `suc (suc zero)`.

```sh
lake exe nbe fragments 'natrec (fst ((\x. (suc x, zero)) zero)) { zero -> suc zero; suc (k, r) -> suc r }'
```

To add an operator family, give it a signature and an `NbE.Fragment` with its
reduction rules. The rules receive the embedding of their own operators into the
containing language. Use `position.project` to match a constructor and
`position.eliminate` to reduce through it. Combine fragments with `Fragment.sum`
and choose the binding patterns for their combined signature. The same pair
and natural rules also run in their standalone demos.

This example adds the function fragment to a sum of pairs and naturals.

```lean
import FreeFoil.Examples.NbEDemos.Program

open FreeFoil FreeFoil.Examples.NbEDemos

def pairAndNaturalRules : NbE.Fragment
    (Pairs.sig.sum Naturals.sig Monolith.Pattern Monolith.Pattern.binders) :=
  Pairs.fragment.sum Naturals.fragment

def mixedRules : NbE.Rules Fragments.sig NbE.NoContext :=
  (Functions.fragment.sum pairAndNaturalRules).rules

#eval (do
  let raw ← (Fragments.parse "fst ((\\x. (suc x, zero)) zero)").toOption
  let term ← (AST.fromClosed raw).toOption
  let normal ← (NbE.nf mixedRules 64 () term).toOption
  pure (Fragments.pretty (normal.toNamed [] fun name => nomatch name.property)) : Option String)
-- some "suc zero"
```

## Define a signature

Import `FreeFoil` for the generic library. A `Signature` gives each operator an arity for ordinary children and an arity for scoped children. Each scoped child has a pattern shape and a list of distinct names in binding order. The pattern shape determines the number of names, so a signature can use zero-name patterns, single binders, or patterns that bind several names. Operator and pattern shape equality are required for `AST.alphaEquiv`.

- `Syntax sig String` represents named syntax. `AST.fromClosed` and `AST.fromNamed` resolve names and report unbound variables or duplicate names in a pattern.
- `AST sig scope` carries a Lean proof that all variable occurrences resolve in the current context. `AST.view` exposes one layer of the tree. `AST.sink` uses context inclusion and reuses the underlying tree in constant time.
- `AST.substitute` refreshes colliding binders as it traverses the input. `ScopedAST.instantiate` accepts one argument for each bound name. `AST.refresh` assigns canonical names to all binders, and `AST.toNamed` makes those names available as strings.
- `AST.freeVars` computes the support, `AST.restrict` checks a smaller context, and `AST.fold` and `AST.hoist` support generic consumers and signature transformations.
- `Telescope` stores labelled binders whose payloads can refer to earlier entries. `Telescope.rename` carries those references into the new scope, and `Telescope.thin` keeps the entries a term uses, including dependencies in their payloads.

## Generate a signature from an inductive

Import `FreeFoil.Derive` and declare an inductive for the named syntax, with a `var` constructor taking a `String`. Use the inductive itself for ordinary recursive positions and `BoundSyntax Pattern Pattern.binders YourInductive` for positions that extend scope. The binder carries its shape and names in binding order.

The [λΠ example](FreeFoil/Examples/LambdaPi.lean) runs `derive_free_foil NamedTerm with Pattern, Pattern.binders` to generate `Op`, `sig`, `Raw`, and `Term` in its namespace. It also generates constructor helpers, a conversion between `NamedTerm` and `Raw`, and `NamedTerm.resolveClosed` to check scope. Constructor helpers for `Raw` take a binder and body separately at each scoped position.

Pass several syntax inductives as `derive_free_foil [SourceTerm, SourceType] with Pattern, Pattern.binders` to generate a shared signature for a family. Constructors can refer to any category in the family in ordinary or scoped positions. A constructor can also carry fixed payloads with decidable equality. The generated reverse conversions return `Option` and check the category of each node and child in the shared tree.

Recursive fields can appear inside any combination of `List` and `Option`, such as `List (Option (Source Literal))`. For scoped fields, put `BoundSyntax Pattern Pattern.binders (Source Literal)` at the leaf. The generated helpers preserve the container shape and order. A nested scoped leaf takes a `(Binder, Raw)` pair in a raw helper and a `ScopedAST` in a checked helper.

A source inductive can declare ordinary type parameters, such as `(Literal : Type)`. The generated `Op Literal`, `sig Literal`, `Raw Literal`, and `Term Literal` retain that parameter. Helpers and conversions infer it from their arguments or result. The operator's derived equality uses the equality instances required by its payloads. All categories in a family must have the same number of parameters, and recursive fields must pass them in the original order. The generated signature uses `Type` at universe zero. Indexed inductives, dependent constructor fields, and recursive containers other than `List` and `Option` are unsupported.

## Second-order abstract syntax

Import `FreeFoil.Examples.SOAS` to build the terms, types, and typing judgments with Lean constructors. `MetaSubst.fromNamed` checks the scope of each replacement and records its ordered parameters. `applySubsts` substitutes metavariable applications simultaneously, and `isSolutionFor` checks whether the resulting sides of each constraint match up to α-equivalence. The suite includes nested substitution and matching examples from the upstream SOAS doctests.

Use `solvePatterns` on equations whose metavariables take distinct variables from the constraint parameters or enclosing binders. Each metavariable has a fixed arity. The solver aligns binders by position and can introduce fresh metavariables when flexible terms share only some of their arguments. For example, solving `?F[x] = f(x)` gives a replacement that applies `f` to the argument of `?F`. A successful `PatternSolution` includes the simultaneous substitution and a Lean proof that `isSolutionFor` accepts it. Repeated or non-variable arguments return `PatternError.nonPattern`. The optional fuel argument bounds the number of worklist steps.

## Run standalone MLTT

```sh
lake exe mltt test/fixtures/mltt/core.mltt
lake exe mltt - < test/fixtures/mltt/core.mltt
```

The interpreter runs the `def`, `check`, and `compute` commands of a standalone program. `compute` infers a type and then fully normalizes the term. The core includes dependent functions and pairs, recursive pair patterns, unit, and identity types with `refl` and `J`. The core follows upstream in using one universe with type-in-type and reports fuel exhaustion when reduction or type checking exceeds its recursion budget.

The test suite runs [the unchanged upstream core fixture](https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/mltt/examples/core.mltt), distributed under the [upstream MLTT license](test/fixtures/mltt/LICENSE).

## Check and link MLTT modules

```sh
lake exe mltt test/fixtures/mltt/parameters.mltt
```

A file can contain several named modules. Each module declares its dependent parameters after its name and lists its direct imports before its commands. A definition is abstracted over just the parameters its type and value need, including the dependencies of those parameters. An optional `over` clause asserts that set. References within the module automatically supply those arguments. Clients pass them explicitly.

An import exposes each declaration by its bare name and by its module-qualified name. A local definition or binder takes precedence over imported names. If an imported spelling refers to several distinct declarations, the interpreter reports an ambiguity when that spelling is used.

Lean clients can call `checkModule` with a half-open `NameRange`. The function allocates declaration identifiers in source order. Use `linkModules` to combine separately checked environments, including branches with a shared dependency. Linking widens the declaration scopes while retaining their identifiers and rejects overlapping reservations or conflicting copies of the same module.

The parameter example is the [unchanged upstream fixture](https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/mltt/examples/parameters.mltt).

### Build a project from several files

```sh
lake exe mltt providers.mltt client.mltt
```

Each file can contribute modules and named telescopes to the project. Imports can refer to modules in any of the supplied files. The build checks dependencies before their clients and assigns identifier ranges by module name, so reordering the paths preserves the build output and identifiers.

Pass `--parallel` to check independent modules concurrently.

```sh
lake exe mltt --parallel providers.mltt client.mltt
```

Each check starts after its imports finish successfully. The build retains the sequential order for reported results and uses the same declaration identifiers. A failing module is reported with its source location, and its clients are skipped. Use `--parallel` for a source build and `--cache` for a build that reuses checked artifacts.

### Share module parameters with named telescopes

Declare a telescope alongside the modules and use `include` before the local parameters in a module or telescope header.

```text
telescope Carrier (A : 𝕌)
telescope Pointed include Carrier (point : A)

module Points include Pointed
def chosen over (A, point) : A := point

module Pairs include Pointed (other : A)
def chosen over (A, other) : A := other
```

The fields of each include appear in their declared order, followed by the local parameters. Each including module checks the expanded header in its own scope. Definitions discharge the parameters they use and the dependencies of those parameters, as with an explicit header. Telescope names can be used before their declaration or from another file in the project. Missing telescopes, include cycles, and repeated parameter names are errors.

### Refine an included telescope

An include can fix fields with `/ {field := value, ...}`.

```text
telescope Choice (A : 𝕌) (point : A)

module UnitChoices include Choice / {A := 𝟙}
def chosen over (point) : A := point

module UnitChoice include Choice / {A := 𝟙, point := tt}
def chosen over () : A := point
```

MLTT checks the assignments in telescope field order with the module's imports and earlier fixed fields in scope. The type and value of a fixed field must be independent of unfixed parameters. Later types and definitions use the fixed values as abbreviations. `UnitChoices.chosen` takes a `𝟙` argument. `UnitChoice.chosen` has type `𝟙` and takes no arguments.

Lean callers can construct an unfixed `Parameter` with `{ name, type }`. The positional constructor takes `fixedValue : Option Raw` as its third field.

## Save and load checked MLTT modules

Import `FreeFoil.Examples.MLTT` to use artifacts from Lean. Call `makeArtifact` on a checked environment and module name, then use `encodeArtifact` to produce a versioned JSON string for storage. Read it with `decodeArtifact` and call `loadArtifact` with the module's dependencies already checked or loaded. The restored module retains its declaration identifiers and can be linked or imported like a module checked from source.

Loading verifies dependency checksums and reservations, resolves bound references and free declaration identifiers, and type-checks declarations in order. The artifact preserves a module's discharged declarations and their imports. It records global identifiers at their existing reservations and uses lexical levels for local binders.

### Reuse checked modules across builds

```sh
lake exe mltt --cache .mltt-cache providers.mltt client.mltt
```

The cache records each module's parsed source after telescope expansion, its checked artifact, and its command output. A subsequent build revalidates matching artifacts against their checked dependencies. Cached modules replay the stored output of `def`, `check`, and `compute` without running those source commands again. Whitespace and comments leave the parsed source unchanged.

An edit rebuilds the affected module. Its clients can still reuse artifacts if their checked dependencies are unchanged up to α-equivalence. The cache retains identifier ranges as unrelated modules are added. A module that outgrows its reservation receives a new range. Missing, stale, or invalid entries fall back to source checking. The build writes replacement entries after the whole project checks successfully.

### Explore checked modules interactively

```sh
lake exe mltt --repl client.mltt providers.mltt
```

After the build succeeds, enter one `import`, `def`, `check`, or `compute` command per line. An import exposes a module's declarations by their bare and qualified names. Import dependencies explicitly to use their names, too. Successful definitions are available until you end the session with EOF. A rejected instruction prints a diagnostic and the session continues.

These commands import and query the `UnitChoice` module from the telescope example.

```text
import UnitChoice
def result : 𝟙 := UnitChoice.chosen
check result : 𝟙
compute result
```

Add `--cache .mltt-cache` after `--repl` to use the artifact cache. If an earlier build has already populated the cache, start a session without source files to import its modules on demand.

```sh
lake exe mltt --repl --cache .mltt-cache
```

The REPL checks each requested artifact with its dependencies before exposing the module. Use `--repl --parallel` to check source modules in parallel before starting a session.

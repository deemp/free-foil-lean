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

## Second-order abstract syntax

Import `FreeFoil.Examples.SOAS` to build the terms, types, and typing judgments with Lean constructors. `MetaSubst.fromNamed` checks the scope of each replacement and records its ordered parameters. `applySubsts` substitutes metavariable applications simultaneously, and `isSolutionFor` checks whether the resulting sides of each constraint match up to α-equivalence. The suite includes nested substitution and matching examples from the upstream SOAS doctests.

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

## Save and load checked MLTT modules

Import `FreeFoil.Examples.MLTT` to use artifacts from Lean. Call `makeArtifact` on a checked environment and module name, then use `encodeArtifact` to produce a versioned JSON string for storage. Read it with `decodeArtifact` and call `loadArtifact` with the module's dependencies already checked or loaded. The restored module retains its declaration identifiers and can be linked or imported like a module checked from source.

Loading verifies dependency checksums and reservations, resolves bound references and free declaration identifiers, and type-checks declarations in order. The artifact preserves a module's discharged declarations and their imports. It records global identifiers at their existing reservations and uses lexical levels for local binders.

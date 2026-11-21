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

This port covers the core library and a λΠ example built directly in Lean. Upstream Template Haskell generators, binary artifacts and module linking, and the SOAS and MLTT applications are outside the current port. Context membership and fresh-name allocation currently use lists. Runtime performance parity with Haskell has not been measured.

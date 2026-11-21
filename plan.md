# Free Foil Lean port plan

Complete the λΠ example, then port the reusable binder machinery and the larger upstream language examples. The current Lean library already provides scope checking, capture-avoiding substitution, α-equivalence, scope restriction, and named-syntax conversion. Use upstream revision `fdfbeef` as the reference for behavior and fixtures. [Lean library README](README.md) · [Upstream Free Foil](https://github.com/fizruk/free-foil/tree/fdfbeef)

## 1. Finish the λΠ example

- Add recursive pair patterns for λ and Π binders. Keep pattern shape and bound names in binding order, and use `ScopedAST.instantiate` with projections to implement β-reduction for pair patterns.
- Parse and pretty-print the upstream λΠ syntax. Add a Lake executable that reads `compute` commands from a file or stdin, resolves names, and prints weak-head normal forms. Keep the existing evaluator's fuel limit and report parse, scope, and evaluation errors to the caller.
- Verify nested pair and wildcard patterns, capture avoidance, duplicate binder rejection, and parse/print round trips up to α-equivalence. Run representative upstream `compute` examples through the executable.

[Lean example](FreeFoil/Examples/LambdaPi.lean) · [Upstream grammar](https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/lambda-pi/grammar/LambdaPi/Syntax.cf) · [Upstream interpreter](https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/lambda-pi/src/Language/LambdaPi/Impl/FreeFoilTH.hs)

## 2. Port telescopes and binder thinning

- Introduce a scope-indexed telescope whose payload at each step can refer to earlier binders. Add operations to extend a scope, rename telescope entries and their payloads together, and compare telescopes up to α-equivalence.
- Port dependency closure and thinning. Given a term's free variables, retain the telescope entries it needs, including dependencies in their types, in the original order. Use the existing support and restriction operations where they apply.
- Verify that thinning `(A : 𝕌) (x : A) (B : 𝕌)` for a term that uses `x` retains `A` and `x`, drops `B`, and leaves the retained payloads and term well scoped.

[Upstream telescope implementation](https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/free-foil/src/Control/Monad/Foil/Telescope.hs)

## 3. Add syntax generation and port SOAS

- Use Lean metaprogramming to generate a `Signature`, constructor helpers, and conversions from a raw syntax declaration. Use the completed λΠ example to validate the first version, including binder positions and duplicate-name diagnostics.
- Extend generation to handle SOAS's mutually recursive term and type categories. Port metavariable substitution, matching, and constraint checking over the generated syntax.
- Verify that the generated λΠ syntax passes the existing evaluation tests and that upstream SOAS fixtures cover both successful matches and constraints that reject a proposed substitution.

[Upstream syntax generator](https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/free-foil/src/Control/Monad/Free/Foil/TH/MkFreeFoil.hs) · [Upstream SOAS README](https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/soas/README.md)

## 4. Port MLTT and checked module artifacts

- Start with the standalone MLTT evaluator and bidirectional type checker. Use upstream core examples to check inference, checking, and definitional equality.
- Add module parameters on top of telescopes, then port reserved name ranges and scope linking. Verify that two independently checked modules with a shared dependency can be linked without renaming their declarations.
- Add serialization and loading of checked modules. Revalidate decoded terms and their references before constructing checked Lean values. Verify round trips, missing dependencies, and invalid or conflicting name allocations.

[Upstream MLTT README](https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/mltt/README.md) · [Upstream scope linking](https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/free-foil/src/Control/Monad/Foil/Blocks.hs) · [Upstream artifact implementation](https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/free-foil/src/Control/Monad/Free/Foil/Artifact.hs)

## Substitution laws

This work can proceed alongside the example ports. Prove that identity substitution preserves a term up to α-equivalence and that applying two substitutions in sequence agrees with applying their composition. State the results for generic signatures, then check that the statements cover open terms and binders that must be refreshed. Use the upstream law suite as the starting point. [Upstream Free Foil laws](https://github.com/fizruk/free-foil/blob/fdfbeef/haskell/free-foil/test/laws/Control/Monad/Free/Foil/Laws.hs#L411)

## Verification

Run `lake build` and `lake test` with the version pinned in `lean-toolchain` for each milestone. Add focused Lean `example`s for proof regressions and use the existing test driver for runtime behavior. For the λΠ executable, also run upstream input fixtures through the parser, evaluator, and printer together.

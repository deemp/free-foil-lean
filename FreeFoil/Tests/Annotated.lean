import FreeFoil.Examples.LambdaPi

namespace FreeFoil.Tests.Annotated

open FreeFoil.Examples.LambdaPi

private abbrev Span := String.Pos.Raw × String.Pos.Raw

private def span : Span := (⟨4⟩, ⟨5⟩)

private def check (message : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError message)

private def checkBody (term : AnnotatedAST sig Span scope) (bound : Nat)
    (annotationSupport : List (List Nat)) : IO Unit := do
  let .node (.original .lam) _ children := term.view
    | throw (IO.userError "annotations changed the lambda's shape")
  let child := children 0
  check "unexpected binder identifiers for an annotated lambda" (child.binder.names == [bound])
  let some (location, terms, body) := AnnotatedAST.annotation? child.body
    | throw (IO.userError "annotation below the binder was lost")
  check "annotation lost its source span" (location == span)
  check "annotation terms did not use the same substitution as the body"
    (terms.map AST.freeVars == annotationSupport && body.freeVars == [bound])

def run : IO Unit := do
  let source : Scope := [0]
  let binder : Binder (sig.annotated Span) Nat := ⟨.variable, [1], rfl⟩
  let bound : Term (binder.names ++ source) := AST.var ⟨1, by simp [binder]⟩
  let ambient : Term (binder.names ++ source) := AST.var ⟨0, by simp [binder, source]⟩
  let body : AnnotatedAST sig Span (binder.names ++ source) :=
    (AnnotatedAST.ofAST bound).annotate span [AnnotatedAST.ofAST bound, AnnotatedAST.ofAST ambient]
  let term : AnnotatedAST sig Span source :=
    AST.node (sig := sig.annotated Span) (.original .lam) Fin.elim0
      fun _ => ⟨binder, by simp [binder], body⟩
  check "erased syntax includes a name used only by an annotation" term.erase.freeVars.isEmpty
  check "support missed a name used only by an annotation" (term.freeVars == [0])
  checkBody term 1 [[1], [0]]

  let .ok plain := AST.fromClosed (Raw.lam "renamed" (Raw.var "renamed"))
    | throw (IO.userError "could not resolve comparison term")
  let comparison : AnnotatedAST sig Unit source := AnnotatedAST.ofAST (plain.sink (by simp))
  check "structural alpha-equivalence compared annotations" (term.alphaEquiv comparison)

  let renamed := term.rename (target := [1]) fun _ => ⟨1, by simp⟩
  checkBody renamed 2 [[2], [1]]
  check "renaming captured an annotation's free identifier" (renamed.freeVars == [1])

  let target : Scope := [1, 3]
  let replacement : Term target :=
    Term.pair (AST.var ⟨1, by simp [target]⟩) (AST.var ⟨3, by simp [target]⟩)
  let substituted := term.substitute target (.mapping fun _ => AnnotatedAST.ofAST replacement)
  checkBody substituted 4 [[4], [1, 3]]
  check "substitution dropped annotation dependencies" (substituted.freeVars == [1, 3])

end FreeFoil.Tests.Annotated

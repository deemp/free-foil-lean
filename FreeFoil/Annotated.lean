import FreeFoil.Alpha

/-!
Attach source locations and scope-checked terms to syntax using `AnnotatedAST`.
For example, a client can record a byte span and an inferred type on a term:

```lean
open FreeFoil

def withInferredType {sig : Signature} {scope : Scope}
    (term inferredType : AST sig scope) (start stop : String.Pos.Raw) :
    AnnotatedAST sig (String.Pos.Raw × String.Pos.Raw) scope :=
  (AnnotatedAST.ofAST term).annotate (start, stop) [AnnotatedAST.ofAST inferredType]
```

An annotation inside a binder can refer to names introduced by that binder.
`AST.rename` and `AST.substitute` traverse both the underlying syntax and the
annotation terms. `AST.freeVars` includes annotation dependencies, while
`AnnotatedAST.alphaEquiv` compares the underlying syntax.
-/

namespace FreeFoil

/-- The operators of a signature with annotation wrappers. -/
inductive AnnotatedOp (sig : Signature) (metadata : Type) where
  | original (op : sig.Op)
  | annotation (data : metadata) (termCount : Nat)

/-- Extend a signature with annotation wrappers. Each wrapper has its subject and
its annotation terms as ordinary children in the same scope. -/
abbrev Signature.annotated (sig : Signature) (metadata : Type) : Signature where
  Op := AnnotatedOp sig metadata
  Pattern := sig.Pattern
  terms
    | .original op => sig.terms op
    | .annotation _ count => count + 1
  scopes
    | .original op => sig.scopes op
    | .annotation _ _ => 0
  binders := sig.binders

/-- Scope-safe syntax carrying optional annotations at any node. -/
abbrev AnnotatedAST (sig : Signature) (metadata : Type) (scope : Scope) :=
  AST (sig.annotated metadata) scope

namespace AnnotatedAST

variable {sig : Signature} {metadata : Type} {scope : Scope}

/-- Embed unannotated syntax in the annotated signature. -/
def ofAST (term : AST sig scope) : AnnotatedAST sig metadata scope :=
  term.hoist (dst := sig.annotated metadata) (fun shape => ⟨shape, rfl⟩)
    fun op => AST.node (sig := sig.annotated metadata) (.original op)

/-- Attach metadata and any scope-checked terms to a node. Multiple annotations
can be attached by repeated calls. -/
def annotate (term : AnnotatedAST sig metadata scope) (data : metadata)
    (terms : List (AnnotatedAST sig metadata scope) := []) :
    AnnotatedAST sig metadata scope :=
  AST.node (.annotation data terms.length) (Fin.cases term fun i => terms[i]) Fin.elim0

/-- Read the outermost annotation and the syntax it annotates. -/
def annotation? (term : AnnotatedAST sig metadata scope) :
    Option (metadata × List (AnnotatedAST sig metadata scope) × AnnotatedAST sig metadata scope) :=
  match term.view with
  | .node (.annotation data count) terms _ =>
    some (data, List.ofFn (n := count) (fun i => terms i.succ), terms 0)
  | _ => none

/-- Drop all annotations and recover the underlying syntax. -/
def erase (term : AnnotatedAST sig metadata scope) : AST sig scope :=
  AST.fold (sig := sig.annotated metadata) (Term := AST sig) (Child := ScopedAST sig) AST.var
    (fun binder distinct body => ⟨⟨binder.shape, binder.names, binder.arity⟩, distinct, body⟩)
    (fun op => match op with
      | .original op => AST.node op
      | .annotation _ _ => fun terms _ => terms 0)
    term

/-- Compare syntax up to binder renaming, ignoring annotations. -/
def alphaEquiv [DecidableEq sig.Op] [DecidableEq sig.Pattern]
    (left : AnnotatedAST sig metadata scope) (right : AnnotatedAST sig otherMetadata scope) : Bool :=
  left.erase.alphaEquiv right.erase

end AnnotatedAST
end FreeFoil

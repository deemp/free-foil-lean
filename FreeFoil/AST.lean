import FreeFoil.Syntax

namespace FreeFoil

/-- Scope-safe syntax. The well-scopedness proof is erased at runtime. -/
structure AST (sig : Signature) (scope : Scope) where
  syntaxTree : Syntax sig Nat
  wellScoped : syntaxTree.WellScoped scope

/-- A scoped child, with the body in the context extended by the pattern's names. -/
structure ScopedAST (sig : Signature) (scope : Scope) where
  binder : Binder sig Nat
  distinct : binder.names.Nodup
  body : AST sig (binder.names ++ scope)

namespace AST

variable {sig : Signature} {scope : Scope}

def var (name : Name scope) : AST sig scope := ⟨.var name.id, name.property⟩

def node (op : sig.Op) (terms : Fin (sig.terms op) → AST sig scope)
    (children : Fin (sig.scopes op) → ScopedAST sig scope) : AST sig scope :=
  ⟨.node op (fun i => (terms i).syntaxTree) (fun i => (children i).binder)
    (fun i => (children i).body.syntaxTree),
    ⟨fun i => (terms i).wellScoped, fun i => ⟨(children i).distinct, (children i).body.wellScoped⟩⟩⟩

/-- A single layer of an AST, with the recursive positions still scope checked. -/
inductive View (sig : Signature) (scope : Scope) where
  | var (name : Name scope)
  | node (op : sig.Op) (terms : Fin (sig.terms op) → AST sig scope)
      (children : Fin (sig.scopes op) → ScopedAST sig scope)

def view (term : AST sig scope) : View sig scope :=
  match term with
  | ⟨.var id, wf⟩ => .var ⟨id, wf⟩
  | ⟨.node op terms binders bodies, wf⟩ => .node op (fun i => ⟨terms i, wf.1 i⟩)
    (fun i => ⟨binders i, (wf.2 i).1, ⟨bodies i, (wf.2 i).2⟩⟩)

/-- Widen the context in constant time, without renaming or visiting any nodes. -/
@[inline] def sink (h : source ⊆ target) (term : AST sig source) : AST sig target :=
  ⟨term.syntaxTree, term.wellScoped.mono h⟩

/-- Scope-check numeric syntax. -/
def ofSyntax (scope : Scope) (term : Syntax sig Nat) : Option (AST sig scope) :=
  match term.check scope with
  | isTrue h => some ⟨term, h⟩
  | isFalse _ => none

/-- Move a term to a new context if it contains every free name the term uses. -/
def restrict (target : Scope) (term : AST sig scope) : Option (AST sig target) :=
  ofSyntax target term.syntaxTree

private def foldSyntax {Term Child : Scope → Type}
    (onVar : ∀ {s}, Name s → Term s)
    (onChild : ∀ {s}, (binder : Binder sig Nat) → binder.names.Nodup →
      Term (binder.names ++ s) → Child s)
    (onNode : ∀ {s}, (op : sig.Op) → (Fin (sig.terms op) → Term s) →
      (Fin (sig.scopes op) → Child s) → Term s)
    {scope : Scope} (term : Syntax sig Nat) (wf : term.WellScoped scope) : Term scope :=
  match term with
  | .var name => onVar ⟨name, wf⟩
  | .node op terms binders bodies => onNode op
      (fun i => foldSyntax onVar onChild onNode (terms i) (wf.1 i))
      (fun i => onChild (binders i) (wf.2 i).1 (foldSyntax onVar onChild onNode (bodies i) (wf.2 i).2))

/-- Fold syntax into a scope-indexed carrier with separate algebras for variables, patterns and nodes. -/
def fold {Term Child : Scope → Type}
    (onVar : ∀ {s}, Name s → Term s)
    (onChild : ∀ {s}, (binder : Binder sig Nat) → binder.names.Nodup →
      Term (binder.names ++ s) → Child s)
    (onNode : ∀ {s}, (op : sig.Op) → (Fin (sig.terms op) → Term s) →
      (Fin (sig.scopes op) → Child s) → Term s)
    (term : AST sig scope) : Term scope :=
  foldSyntax onVar onChild onNode term.syntaxTree term.wellScoped

/-- Transform a term into another signature, preserving the arity of each binding pattern. -/
def hoist {dst : Signature} (term : AST sig scope)
    (onPattern : (shape : sig.Pattern) → { p : dst.Pattern // dst.binders p = sig.binders shape })
    (onNode : ∀ {s}, (op : sig.Op) → (Fin (sig.terms op) → AST dst s) →
      (Fin (sig.scopes op) → ScopedAST dst s) → AST dst s) : AST dst scope :=
  term.fold (Term := AST dst) (Child := ScopedAST dst) AST.var
    (fun binder distinct body =>
      let shape := onPattern binder.shape
      ⟨⟨shape.val, binder.names, binder.arity.trans shape.property.symm⟩, distinct, body⟩)
    onNode

/-- Collect the free identifiers in order of first occurrence. -/
def freeVars (term : AST sig scope) : List Nat :=
  (term.fold (Term := fun _ => List Nat) (Child := fun _ => List Nat)
    (fun name => [name.id])
    (fun binder _ body => body.filter fun id => !binder.names.contains id)
    (fun _ terms children =>
      (List.ofFn terms).flatten ++ (List.ofFn children).flatten)).eraseDups

end AST
end FreeFoil

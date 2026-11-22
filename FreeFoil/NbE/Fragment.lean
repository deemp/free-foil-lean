import FreeFoil.NbE

namespace FreeFoil

/-- Disjoint operator families with a common vocabulary of binding patterns. -/
abbrev Signature.sum (left right : Signature) (Pattern : Type) (binders : Pattern → Nat) :
    Signature where
  Op := Sum left.Op right.Op
  Pattern := Pattern
  terms := Sum.elim left.terms right.terms
  scopes := Sum.elim left.scopes right.scopes
  binders := binders

/-- The position of a fragment's operators in a language. Ordinary and scoped
children retain their arities. Each operator must have its own tag. -/
structure Signature.Embedding (part whole : Signature) where
  op : part.Op → whole.Op
  terms : ∀ tag, whole.terms (op tag) = part.terms tag
  scopes : ∀ tag, whole.scopes (op tag) = part.scopes tag

namespace Signature.Embedding

variable {part middle whole l r : Signature} {Pattern : Type} {binders : Pattern → Nat}

def identity (sig : Signature) : sig.Embedding sig :=
  ⟨id, fun _ => rfl, fun _ => rfl⟩

def left : l.Embedding (l.sum r Pattern binders) :=
  ⟨Sum.inl, fun _ => rfl, fun _ => rfl⟩

def right : r.Embedding (l.sum r Pattern binders) :=
  ⟨Sum.inr, fun _ => rfl, fun _ => rfl⟩

def trans (inner : part.Embedding middle) (outer : middle.Embedding whole) :
    part.Embedding whole :=
  ⟨outer.op ∘ inner.op, fun tag => (outer.terms _).trans (inner.terms tag),
    fun tag => (outer.scopes _).trans (inner.scopes tag)⟩

private def reindex (equal : first = second) (positions : Fin second → α) : Fin first → α :=
  fun i => positions (Fin.cast equal i)

/-- Transform the syntax of a term, preserving binding and child order. -/
def mapSyntax (position : part.Embedding whole)
    (shape : (p : part.Pattern) → { q : whole.Pattern // whole.binders q = part.binders p }) :
    Syntax part α → Syntax whole α
  | .var name => .var name
  | .node op terms binders bodies =>
    .node (position.op op)
      (fun i => position.mapSyntax shape (terms (Fin.cast (position.terms op) i)))
      (fun i =>
        let binder := binders (Fin.cast (position.scopes op) i)
        let mapped := shape binder.shape
        ⟨mapped.val, binder.names, binder.arity.trans mapped.property.symm⟩)
      (fun i => position.mapSyntax shape (bodies (Fin.cast (position.scopes op) i)))

/-- Transform a checked term into a language with the same free names. -/
def mapAST (position : part.Embedding whole)
    (shape : (p : part.Pattern) → { q : whole.Pattern // whole.binders q = part.binders p })
    (term : AST part scope) : AST whole scope :=
  term.hoist shape fun op terms children =>
    AST.node (position.op op) (reindex (position.terms op) terms) (reindex (position.scopes op) children)

open NbE

/-- Construct an ambient thunk from the fragment's own operators and positions. -/
def node (position : part.Embedding whole) (op : part.Op)
    (terms : Fin (part.terms op) → Thunk whole scope)
    (children : Fin (part.scopes op) → Closure whole scope) : Thunk whole scope :=
  .node (position.op op) (reindex (position.terms op) terms) (reindex (position.scopes op) children)

/-- Match an ambient head against one of the fragment's own operators. -/
def project (position : part.Embedding whole) [DecidableEq whole.Op] (op : part.Op)
    (value : Value whole scope) :
    Option ((Fin (part.terms op) → Thunk whole scope) × (Fin (part.scopes op) → Closure whole scope)) :=
  match value with
  | .node tag terms children =>
    if equal : position.op op = tag then
      some (reindex ((position.terms op).symm.trans (congrArg whole.terms equal)) terms,
        reindex ((position.scopes op).symm.trans (congrArg whole.scopes equal)) children)
    else none
  | _ => none

/-- Run a principal-operand reduction, keeping definition unfolding available. -/
def eliminate (position : part.Embedding whole) (evaluator : Evaluator whole scope)
    (op : part.Op) (terms : Fin (part.terms op) → Thunk whole scope)
    (children : Fin (part.scopes op) → Closure whole scope) (principal : Fin (part.terms op))
    (reduce : Value whole scope → Result (Option (Value whole scope))) :
    Result (Option (Value whole scope)) :=
  evaluator.eliminate (position.op op) (reindex (position.terms op) terms)
    (reindex (position.scopes op) children) (Fin.cast (position.terms op).symm principal) reduce

end Signature.Embedding

namespace NbE

/-- Rules for an operator family, polymorphic in the language that contains it. -/
structure Fragment (part : Signature) where
  reduce : ∀ {whole scope} [DecidableEq whole.Op], part.Embedding whole →
    Evaluator whole scope → (op : part.Op) → (Fin (part.terms op) → Thunk whole scope) →
      (Fin (part.scopes op) → Closure whole scope) → Result (Option (Value whole scope)) :=
    fun _ _ _ _ _ => pure none
  isHead : (op : part.Op) → Fin (part.terms op) → Bool := fun _ _ => false
  eta : ∀ {whole}, (position : part.Embedding whole) → (op : part.Op) →
    Option (EtaObservers whole NoContext (position.op op)) := fun _ _ => none

/-- Combine two independent operator families over the same binding patterns. -/
def Fragment.sum {Pattern : Type} {binders : Pattern → Nat}
    (left : Fragment l) (right : Fragment r) : Fragment (l.sum r Pattern binders) where
  reduce position evaluator op :=
    match op with
    | .inl tag => left.reduce (Signature.Embedding.left.trans position) evaluator tag
    | .inr tag => right.reduce (Signature.Embedding.right.trans position) evaluator tag
  isHead op := match op with
    | .inl tag => left.isHead tag
    | .inr tag => right.isHead tag
  eta position op := match op with
    | .inl tag => left.eta (Signature.Embedding.left.trans position) tag
    | .inr tag => right.eta (Signature.Embedding.right.trans position) tag

/-- Run a fragment, or a sum of fragments, as a language. -/
def Fragment.rules {sig : Signature} [DecidableEq sig.Op] (fragment : Fragment sig) :
    Rules sig NoContext where
  reduce evaluator _ := fragment.reduce (Signature.Embedding.identity sig) evaluator
  extend _ _ _ _ _ _ := pure ()
  isHead := fragment.isHead
  eta := fragment.eta (Signature.Embedding.identity sig)

end NbE
end FreeFoil

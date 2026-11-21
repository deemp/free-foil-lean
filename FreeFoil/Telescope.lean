import FreeFoil.Alpha

namespace FreeFoil

/-- A sequence of labelled binders extending `outer` to `inner`.
Each payload lives in the scope of the preceding entries. -/
inductive Telescope (Label : Type) (Payload : Scope → Type) : (outer inner : Scope) → Type where
  | nil : Telescope Label Payload scope scope
  | cons (label : Label) (payload : Payload scope) (id : Nat) (fresh : id ∉ scope)
      (rest : Telescope Label Payload (id :: scope) inner) : Telescope Label Payload scope inner

namespace Telescope

variable {Label : Type} {Payload : Scope → Type} {outer inner : Scope} {sig : Signature}

/-- The scope after extending the ambient scope with all entries. -/
def extendScope (_ : Telescope Label Payload outer inner) : Scope := inner

theorem scopeSubset (telescope : Telescope Label Payload outer inner) : outer ⊆ inner := by
  induction telescope with
  | nil => exact fun {_} mem => mem
  | cons _ _ _ _ _ ih => exact fun {_} mem => ih (List.mem_cons_of_mem _ mem)

/-- The renamed telescope and the lifted renaming for terms in its final scope. -/
structure Renamed (Label : Type) (Payload : Scope → Type) (target sourceInner : Scope) where
  scope : Scope
  telescope : Telescope Label Payload target scope
  renameName : Name sourceInner → Name scope

/-- Rename each payload in its prefix scope and extend the renaming with a fresh binder.
`renamePayload` transports a payload along the given name map. -/
def rename {outer inner : Scope} (telescope : Telescope Label Payload outer inner) (target : Scope)
    (renameName : Name outer → Name target)
    (renamePayload : ∀ {source target}, (Name source → Name target) → Payload source → Payload target) :
    Renamed Label Payload target inner :=
  match telescope with
  | .nil => ⟨target, .nil, renameName⟩
  | .cons label payload id _ rest =>
    let fresh := Scope.fresh target
    let renamed := rest.rename (fresh.id :: target) (fun name =>
      if bound : name.id = id then fresh
      else
        let old : Name _ := ⟨name.id, (List.mem_cons.mp name.property).resolve_left bound⟩
        (renameName old).sink (List.subset_cons_self _ _)) renamePayload
    ⟨renamed.scope, .cons label (renamePayload renameName payload) fresh.id
      (Scope.nextId_not_mem target) renamed.telescope, renamed.renameName⟩

private def alphaEq [DecidableEq sig.Op] [DecidableEq sig.Pattern] {outer inner outer' inner' : Scope}
    (left : Telescope Label (AST sig) outer inner) (right : Telescope Label (AST sig) outer' inner')
    (bindings : List (Nat × Nat)) : Bool :=
  match left, right with
  | .nil, .nil => true
  | .cons _ payload id _ rest, .cons _ payload' id' _ rest' =>
    payload.alphaEquivUnder payload' bindings && alphaEq rest rest' ((id, id') :: bindings)
  | _, _ => false

/-- Compare telescope payloads under their corresponding earlier binders. Labels are ignored. -/
def alphaEquiv [DecidableEq sig.Op] [DecidableEq sig.Pattern]
    (left : Telescope Label (AST sig) outer inner) (right : Telescope Label (AST sig) outer inner') :
    Bool :=
  alphaEq left right []

/-- Add the dependencies of each needed entry, visiting the last entry first.
`support` supplies the free identifiers of a payload. Only membership in the result matters. -/
def closeSupport {outer inner : Scope} (telescope : Telescope Label Payload outer inner)
    (wanted : List Nat) (support : ∀ {scope}, Payload scope → List Nat) : List Nat :=
  match telescope with
  | .nil => wanted
  | .cons _ payload id _ rest =>
    let needed := rest.closeSupport wanted support
    if id ∈ needed then support payload ++ needed else needed

private def restrictTo {outer inner : Scope}
    (telescope : Telescope Label (AST sig) outer inner) (wanted : List Nat)
    (target : Scope) (h : target ⊆ outer) :
    Option ((scope : Scope) × Telescope Label (AST sig) target scope) :=
  match telescope with
  | .nil => some ⟨target, .nil⟩
  | .cons label payload id fresh rest =>
    if id ∈ wanted then do
      let payload ← payload.restrict target
      let ⟨scope, rest⟩ ← rest.restrictTo wanted (id :: target) (List.cons_subset_cons id h)
      pure ⟨scope, .cons label payload id (fun mem => fresh (h mem)) rest⟩
    else
      rest.restrictTo wanted target (List.subset_cons_of_subset id h)

/-- Keep the entries needed by a set of free identifiers, together with their dependencies.
The ambient scope is preserved. Retained entries keep their identifiers and declaration order. -/
def thinToSupport (telescope : Telescope Label (AST sig) outer inner) (wanted : List Nat) :
    Option ((scope : Scope) × Telescope Label (AST sig) outer scope) :=
  telescope.restrictTo (telescope.closeSupport wanted AST.freeVars) outer (fun {_} mem => mem)

/-- A term and the telescope it needs, sharing the same reduced scope. -/
structure Thinned (Label : Type) (sig : Signature) (outer : Scope) where
  scope : Scope
  telescope : Telescope Label (AST sig) outer scope
  term : AST sig scope

/-- Thin a telescope to the support of a term and restrict the term to the resulting scope. -/
def thin (telescope : Telescope Label (AST sig) outer inner) (term : AST sig inner) :
    Option (Thinned Label sig outer) := do
  let ⟨scope, telescope⟩ ← telescope.thinToSupport term.freeVars
  let term ← term.restrict scope
  pure ⟨scope, telescope, term⟩

end Telescope
end FreeFoil

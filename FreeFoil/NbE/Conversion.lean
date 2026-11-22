import FreeFoil.NbE

namespace FreeFoil.NbE

variable {sig : Signature} {Context : Scope → Type}

private abbrev Compare (sig : Signature) (Context : Scope → Type) :=
  ∀ {scope}, Context scope → Bool → Value sig scope → Value sig scope → Result Bool

private def compareNodes [DecidableEq sig.Pattern] (rules : Rules sig Context) (fuel : Nat)
    (compare : Compare sig Context) (ctx : Context scope) (op : sig.Op)
    (leftTerms rightTerms : Fin (sig.terms op) → Thunk sig scope)
    (leftChildren rightChildren : Fin (sig.scopes op) → Closure sig scope) : Result Bool := do
  let sameTerms ← (List.finRange (sig.terms op)).allM fun i => do
    let left ← force rules fuel ctx (leftTerms i)
    let right ← force rules fuel ctx (rightTerms i)
    compare ctx (!rules.isHead op i) left right
  if !sameTerms then return false
  (List.finRange (sig.scopes op)).allM fun i => do
    let left := leftChildren i
    let right := rightChildren i
    if shapes : left.binder.shape = right.binder.shape then
      let binder := left.freshBinder
      let rightArity := binder.property.1.trans <|
        left.binder.arity.trans <| (congrArg sig.binders shapes).trans right.binder.arity.symm
      let inner ← rules.extend ⟨force rules fuel ctx⟩ ctx op leftTerms i binder.val
      let left ← force rules fuel inner (left.openWith binder.val.names binder.property.1)
      let right ← force rules fuel inner (right.openWith binder.val.names rightArity)
      compare inner true left right
    else
      pure false

private def compareEta (rules : Rules sig Context) (fuel : Nat) (compare : Compare sig Context)
    (ctx : Context scope) (intro other : Value sig scope) : Result Bool := do
  let .node op terms children := intro | return false
  let some observers := rules.eta op | return false
  let sameTerms ← (List.finRange (sig.terms op)).allM fun i => do
    let left ← force rules fuel ctx (terms i)
    let right ← force rules fuel ctx (observers.term i ctx other)
    compare ctx true left right
  if !sameTerms then return false
  (List.finRange (sig.scopes op)).allM fun i => do
    let child := children i
    let binder := child.freshBinder
    let inner ← rules.extend ⟨force rules fuel ctx⟩ ctx op terms i binder.val
    let other := other.sink (fun {_} mem => List.mem_append_right _ mem)
    let some observed := observers.body i binder.val inner other | return false
    let left ← force rules fuel inner (child.openWith binder.val.names binder.property.1)
    let right ← force rules fuel inner observed
    compare inner true left right

private inductive ComparisonMode where
  | rigid
  | folded
  | unfolded
  deriving BEq

private def compareValues [DecidableEq sig.Op] [DecidableEq sig.Pattern]
    (rules : Rules sig Context) (fuel : Nat) (ctx : Context scope) (refine : Bool)
    (mode : ComparisonMode)
    (left right : Value sig scope) : Result Bool :=
  match fuel with
  | 0 => .error .outOfFuel
  | fuel + 1 => do
    let evaluator : Evaluator sig scope := ⟨force rules fuel ctx⟩
    let left ← if refine then rules.refineHead evaluator ctx left else pure left
    let right ← if refine then rules.refineHead evaluator ctx right else pure right
    let compare : Compare sig Context := fun ctx refine => compareValues rules fuel ctx refine mode
    match left, right with
    | .glued x leftFolded leftBody, .glued y rightFolded rightBody => do
      if mode == .folded then
        if x != y then return false
        return ← compare ctx refine leftFolded rightFolded
      let tryFolded := mode == .rigid && x == y
      if tryFolded then
        match compareValues rules fuel ctx refine .folded leftFolded rightFolded with
        | .ok true => return true
        | _ => pure ()
      let next := if tryFolded then .unfolded else mode
      let left ← evaluator.force leftBody
      let right ← evaluator.force rightBody
      compareValues rules fuel ctx refine next left right
    | .glued _ _ body, right => do
      if mode == .folded then return false
      let left ← evaluator.force body
      compare ctx refine left right
    | left, .glued _ _ body => do
      if mode == .folded then return false
      let right ← evaluator.force body
      compare ctx refine left right
    | .var x, .var y => pure (x == y)
    | .node op leftTerms leftChildren, .node op' rightTerms rightChildren =>
      if same : op' = op then
        compareNodes rules fuel compare ctx op leftTerms (same ▸ rightTerms)
          leftChildren (same ▸ rightChildren)
      else
        compareDifferentHeads rules fuel compare ctx left right
    | _, _ => compareDifferentHeads rules fuel compare ctx left right
where
  compareDifferentHeads (rules : Rules sig Context) (fuel : Nat) (compare : Compare sig Context)
      (ctx : Context scope) (left right : Value sig scope) : Result Bool := do
    if ← compareEta rules fuel compare ctx left right then return true
    compareEta rules fuel (fun ctx refine intro observed => compare ctx refine observed intro)
      ctx right left

/-- Compare semantic values directly. Matching heads compare their children on
demand, opening corresponding binders with the same fresh names. Two uses of a
definition try their folded forms before comparing unfolded bodies. A language
can opt introductions into η comparison through its rules. -/
def conv [DecidableEq sig.Op] [DecidableEq sig.Pattern]
    (rules : Rules sig Context) (fuel : Nat) (ctx : Context scope)
    (left right : Value sig scope) : Result Bool :=
  compareValues rules fuel ctx true .rigid left right

/-- Evaluate both terms under their own environments and compare in their common
target scope. The budget bounds recursive evaluation and comparison depth. -/
def convertibleUnder [DecidableEq sig.Op] [DecidableEq sig.Pattern]
    (rules : Rules sig Context) (fuel : Nat) (ctx : Context scope)
    (leftEnv : Name source₁ → Thunk sig scope) (rightEnv : Name source₂ → Thunk sig scope)
    (left : AST sig source₁) (right : AST sig source₂) : Result Bool := do
  let left ← evalUnder rules fuel ctx leftEnv left
  let right ← evalUnder rules fuel ctx rightEnv right
  conv rules fuel ctx left right

/-- Compare terms in a common context, resolving their free names through it. -/
def convertible [DecidableEq sig.Op] [DecidableEq sig.Pattern]
    (rules : Rules sig Context) (fuel : Nat) (ctx : Context scope)
    (left right : AST sig scope) : Result Bool :=
  convertibleUnder rules fuel ctx Thunk.free Thunk.free left right

end FreeFoil.NbE

import FreeFoil.Substitution

namespace FreeFoil.NbE

mutual

/-- A semantic head with suspended children. A stuck elimination is a node too. -/
inductive Value (sig : Signature) (scope : Scope) where
  | var (name : Name scope)
  | node (op : sig.Op) (terms : Fin (sig.terms op) → Thunk sig scope)
      (children : Fin (sig.scopes op) → Closure sig scope)

/-- An ordinary argument can be evaluated on demand in its captured environment. -/
inductive Thunk (sig : Signature) (scope : Scope) where
  | ready (value : Value sig scope)
  | syntax {source : Scope} (term : AST sig source) (env : Name source → Thunk sig scope)
  | node (op : sig.Op) (terms : Fin (sig.terms op) → Thunk sig scope)
      (children : Fin (sig.scopes op) → Closure sig scope)

/-- A scoped argument's body and the environment of its free variables. -/
inductive Closure (sig : Signature) (scope : Scope) where
  | mk {source : Scope} (child : ScopedAST sig source) (env : Name source → Thunk sig scope)

end

def Closure.binder (closure : Closure sig scope) : Binder sig Nat :=
  match closure with
  | .mk child _ => child.binder

def Thunk.var (name : Name scope) : Thunk sig scope := .ready (.var name)

mutual

/-- Widen the output scope of a value. Children are weakened when demanded. -/
def Value.sink (value : Value sig source) (included : source ⊆ target) : Value sig target :=
  match value with
  | .var name => .var (name.sink included)
  | .node op terms children =>
    .node op (fun i => (terms i).sink included) (fun i => (children i).sink included)

def Thunk.sink (thunk : Thunk sig source) (included : source ⊆ target) : Thunk sig target :=
  match thunk with
  | .ready value => .ready (value.sink included)
  | .syntax term env => .syntax term fun name => (env name).sink included
  | .node op terms children =>
    .node op (fun i => (terms i).sink included) (fun i => (children i).sink included)

def Closure.sink (closure : Closure sig source) (included : source ⊆ target) : Closure sig target :=
  match closure with
  | .mk child env => .mk child fun name => (env name).sink included

end

private def extendEnv {Carrier : Type} (env : Name source → Carrier) (names : List Nat)
    (args : Fin names.length → Carrier) : Name (names ++ source) → Carrier :=
  fun name =>
    if bound : name.id ∈ names then
      args ⟨names.idxOf name.id, List.idxOf_lt_length_of_mem bound⟩
    else
      env ⟨name.id, (List.mem_append.mp name.property).resolve_left bound⟩

/-- Bind one suspended argument per name, in the order of the pattern. -/
def Closure.instantiate (closure : Closure sig scope)
    (args : Fin closure.binder.names.length → Thunk sig scope) : Thunk sig scope :=
  match closure with
  | .mk child env => .syntax child.body (extendEnv env child.binder.names args)

/-- Choose a binder of the same shape whose names are distinct and fresh for the output scope. -/
def Closure.freshBinder (closure : Closure sig scope) :
    { binder : Binder sig Nat //
      binder.names.length = closure.binder.names.length ∧ binder.names.Nodup ∧
        ∀ name ∈ binder.names, name ∉ scope } :=
  let oldBinder := closure.binder
  let names := scope.freshen false oldBinder.names
  ⟨⟨oldBinder.shape, names.val, names.property.1.trans oldBinder.arity⟩, names.property⟩

/-- Open a closure with the supplied fresh names. Using the same names for two
closures allows a client to compare their bodies in one scope. -/
def Closure.openWith (closure : Closure sig scope) (names : List Nat)
    (arity : names.length = closure.binder.names.length) :
    Thunk sig (names ++ scope) :=
  match closure with
  | .mk child env =>
    let outer name := (env name).sink (fun {_} mem => List.mem_append_right _ mem)
    let neutral i :=
      let j : Fin names.length := Fin.cast arity.symm i
      Thunk.var ⟨names[j], List.mem_append_left _ (List.getElem_mem j.isLt)⟩
    .syntax child.body (extendEnv outer child.binder.names neutral)

inductive Error where
  | outOfFuel
  deriving DecidableEq, Repr

abbrev Result := Except Error

/-- Context for languages that need only the scope. -/
abbrev NoContext (_ : Scope) := Unit

/-- Operations available to an elimination rule at its current scope. Each
recursive call works with a smaller evaluation budget. -/
structure Evaluator (sig : Signature) (scope : Scope) where
  force : Thunk sig scope → Result (Value sig scope)

/-- Demand a scoped body with an argument per bound name. -/
def Evaluator.instantiate (evaluator : Evaluator sig scope) (closure : Closure sig scope)
    (args : Fin closure.binder.names.length → Thunk sig scope) : Result (Value sig scope) :=
  evaluator.force (closure.instantiate args)

/-- A language supplies its eliminations and any information needed under binders.
The default rule keeps a node suspended. Refinement can be used for type-directed
readback. Principal operands read back without refining their own heads. -/
structure Rules (sig : Signature) (Context : Scope → Type) where
  reduce : ∀ {scope}, Evaluator sig scope → Context scope →
    (op : sig.Op) → (Fin (sig.terms op) → Thunk sig scope) →
      (Fin (sig.scopes op) → Closure sig scope) → Result (Option (Value sig scope)) :=
    fun _ _ _ _ _ => pure none
  extend : ∀ {scope}, Evaluator sig scope → Context scope →
    (op : sig.Op) → (Fin (sig.terms op) → Thunk sig scope) →
      Fin (sig.scopes op) → (binder : Binder sig Nat) → Result (Context (binder.names ++ scope))
  refine : ∀ {scope}, Evaluator sig scope → Context scope → Value sig scope → Result (Value sig scope) :=
    fun _ _ value => pure value
  isHead : (op : sig.Op) → Fin (sig.terms op) → Bool := fun _ _ => false

/-- Use elimination rules without a client context. -/
def Rules.scopeOnly
    (reduce : ∀ {scope}, Evaluator sig scope → NoContext scope →
      (op : sig.Op) → (Fin (sig.terms op) → Thunk sig scope) →
        (Fin (sig.scopes op) → Closure sig scope) → Result (Option (Value sig scope))) :
    Rules sig NoContext where
  reduce
  extend _ _ _ _ _ _ := pure ()

private def suspend (term : AST sig source) (env : Name source → Thunk sig scope) : Thunk sig scope :=
  match term.view with
  | .var name => env name
  | .node op terms children => .node op (fun i => .syntax (terms i) env)
    (fun i => .mk (children i) env)

/-- Demand a semantic head. The fuel bounds recursive evaluation depth. -/
def force (rules : Rules sig Context) (fuel : Nat) (ctx : Context scope)
    (thunk : Thunk sig scope) : Result (Value sig scope) :=
  match fuel with
  | 0 => .error .outOfFuel
  | fuel + 1 =>
    let evaluator : Evaluator sig scope := ⟨force rules fuel ctx⟩
    match thunk with
    | .ready value => pure value
    | .syntax term env => evaluator.force (suspend term env)
    | .node op terms children => do
      let result ← rules.reduce evaluator ctx op terms children
      pure (result.getD (.node op terms children))

/-- Evaluate a term in a supplied semantic environment. -/
def evalUnder (rules : Rules sig Context) (fuel : Nat) (ctx : Context scope)
    (env : Name source → Thunk sig scope) (term : AST sig source) : Result (Value sig scope) :=
  force rules fuel ctx (suspend term env)

/-- Evaluate a scope-checked term with its free names as neutrals. -/
def eval (rules : Rules sig Context) (fuel : Nat) (ctx : Context scope)
    (term : AST sig scope) : Result (Value sig scope) :=
  evalUnder rules fuel ctx Thunk.var term

private def mapPositions (f : Fin n → Result α) : Result (Fin n → α) := do
  let values ← (Vector.ofFn id : Vector (Fin n) n).mapM f
  pure (fun i => values[i])

/-- Replace free variables with their frozen terms while leaving the syntax's
reductions untouched. Freshening avoids capture even in previously sunk terms. -/
private def freezeSyntax (term : AST sig source) (target : Scope)
    (env : Name source → Result (AST sig target)) : Result (AST sig target) :=
  term.fold
    (Term := fun s => (t : Scope) → (Name s → Result (AST sig t)) → Result (AST sig t))
    (Child := fun s => (t : Scope) → (Name s → Result (AST sig t)) → Result (ScopedAST sig t))
    (fun name _ env => env name)
    (fun binder _ body scope env => do
      let names := scope.freshen false binder.names
      let newBinder : Binder sig Nat := ⟨binder.shape, names.val, names.property.1.trans binder.arity⟩
      let outer name := (env name).map (AST.sink (fun {_} mem => List.mem_append_right _ mem))
      let neutral i :=
        let j : Fin names.val.length := Fin.cast names.property.1.symm i
        pure (AST.var ⟨names.val[j], List.mem_append_left _ (List.getElem_mem j.isLt)⟩)
      let body ← body _ (extendEnv outer binder.names neutral)
      pure ⟨newBinder, names.property.2.1, body⟩)
    (fun op terms children scope env => do
      let terms ← mapPositions (fun i => terms i scope env)
      let children ← mapPositions (fun i => children i scope env)
      pure (AST.node op terms children))
    target env

private def freezeClosure (closure : Closure sig scope) (names : List Nat)
    (arity : names.length = closure.binder.names.length)
    (read : Thunk sig scope → Result (AST sig scope)) : Result (AST sig (names ++ scope)) :=
  match closure with
  | .mk child env =>
    let outer name := (read (env name)).map (AST.sink (fun {_} mem => List.mem_append_right _ mem))
    let neutral i :=
      let j : Fin names.length := Fin.cast arity.symm i
      pure (AST.var ⟨names[j], List.mem_append_left _ (List.getElem_mem j.isLt)⟩)
    freezeSyntax child.body _ (extendEnv outer child.binder.names neutral)

private def readback (rules : Rules sig Context) (fuel : Nat) (ctx : Context scope)
    (underBinders refine : Bool) (value : Value sig scope) : Result (AST sig scope) :=
  match fuel with
  | 0 => .error .outOfFuel
  | fuel + 1 => do
    let evaluator : Evaluator sig scope := ⟨force rules fuel ctx⟩
    let value ← if refine then rules.refine evaluator ctx value else pure value
    match value with
    | .var name => pure (.var name)
    | .node op terms children =>
      let readTerm i := do
        let value ← evaluator.force (terms i)
        readback rules fuel ctx true (!rules.isHead op i) value
      let readChild i := do
        let closure := children i
        let binder := closure.freshBinder
        let body ← if underBinders then do
          let inner ← rules.extend evaluator ctx op terms i binder.val
          let value ← force rules fuel inner (closure.openWith binder.val.names binder.property.1)
          readback rules fuel inner true true value
        else
          freezeClosure closure binder.val.names binder.property.1 fun thunk => do
            let value ← evaluator.force thunk
            readback rules fuel ctx true false value
        pure (⟨binder.val, binder.property.2.1, body⟩ : ScopedAST sig scope)
      let terms ← mapPositions readTerm
      let children ← mapPositions readChild
      pure (AST.node op terms children)

/-- Fully read back a semantic value, evaluating under each binder. -/
def quote (rules : Rules sig Context) (fuel : Nat) (ctx : Context scope)
    (value : Value sig scope) : Result (AST sig scope) :=
  readback rules fuel ctx true true value

/-- Read back a value's head, freezing its scoped bodies. Ordinary arguments
that are not principal operands are read back fully, as in the upstream API. -/
def quoteWhnf (rules : Rules sig Context) (fuel : Nat) (ctx : Context scope)
    (value : Value sig scope) : Result (AST sig scope) :=
  readback rules fuel ctx false true value

/-- Fully normalize using the language's reduction and readback rules. -/
def nf (rules : Rules sig Context) (fuel : Nat) (ctx : Context scope)
    (term : AST sig scope) : Result (AST sig scope) :=
  eval rules fuel ctx term >>= quote rules fuel ctx

/-- Normalize the head while leaving redexes under its binders suspended. -/
def whnf (rules : Rules sig Context) (fuel : Nat) (ctx : Context scope)
    (term : AST sig scope) : Result (AST sig scope) :=
  eval rules fuel ctx term >>= quoteWhnf rules fuel ctx

end FreeFoil.NbE

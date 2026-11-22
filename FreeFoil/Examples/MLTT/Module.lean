import FreeFoil.Examples.MLTT.Program

namespace FreeFoil.Examples.MLTT

/-- The half-open interval of identifiers reserved for a module's declarations. -/
structure NameRange where
  start : Nat
  stop : Nat
  deriving Repr, DecidableEq

def NameRange.overlaps (left right : NameRange) : Bool :=
  left.start < right.stop && right.start < left.stop

structure CheckedDeclaration (scope : Scope) where
  name : String
  key : Name scope
  parameters : List String

structure CheckedModule (scope : Scope) where
  name : String
  range : NameRange
  imports : Array String
  declarations : List (CheckedDeclaration scope)

/-- A scope and context containing checked, fully discharged declarations.
Each module's imports and reserved range are retained when environments are linked. -/
structure CheckedModules where
  private mk ::
  scope : Scope
  context : Context scope
  modules : List (CheckedModule scope)

namespace CheckedModules

def empty : CheckedModules := ⟨[], .empty, []⟩

def find? (env : CheckedModules) (name : String) : Option (CheckedModule env.scope) :=
  env.modules.find? (·.name == name)

end CheckedModules

private def CheckedDeclaration.sink (decl : CheckedDeclaration source) (h : source ⊆ target) :
    CheckedDeclaration target :=
  ⟨decl.name, decl.key.sink h, decl.parameters⟩

private def CheckedModule.sink (mod : CheckedModule source) (h : source ⊆ target) :
    CheckedModule target :=
  ⟨mod.name, mod.range, mod.imports, mod.declarations.map (·.sink h)⟩

private def unionScope (left right : Scope) : Scope :=
  left ++ right.filter fun id => decide (id ∉ left)

private theorem leftInUnion (left right : Scope) : left ⊆ unionScope left right :=
  fun {_} mem => List.mem_append_left _ mem

private theorem rightInUnion (left right : Scope) : right ⊆ unionScope left right := by
  intro id mem
  by_cases inside : id ∈ left
  · exact List.mem_append_left _ inside
  · exact List.mem_append_right _ (List.mem_filter.mpr ⟨mem, by simp [inside]⟩)

private theorem memSides {left right : Scope} (key : Name (unionScope left right)) :
    key.id ∈ left ∨ key.id ∈ right :=
  (List.mem_append.mp key.property).imp_right fun mem => (List.mem_filter.mp mem).1

private def Context.union (left : Context source) (right : Context target) :
    Context (unionScope source target) where
  typeOf key :=
    if mem : key.id ∈ source then
      (left.typeOf ⟨key.id, mem⟩).sink (leftInUnion source target)
    else
      (right.typeOf ⟨key.id, (memSides key).resolve_left mem⟩).sink (rightInUnion source target)
  definitions key :=
    if mem : key.id ∈ source then
      (left.definitions ⟨key.id, mem⟩).map (AST.sink (leftInUnion source target))
    else
      (right.definitions ⟨key.id, (memSides key).resolve_left mem⟩).map
        (AST.sink (rightInUnion source target))

private def CheckedModule.agrees (left : CheckedModule source) (right : CheckedModule target)
    (leftCtx : Context source) (rightCtx : Context target) : Bool :=
  left.range == right.range && left.imports == right.imports &&
    left.declarations.length == right.declarations.length &&
    (left.declarations.zip right.declarations).all fun (a, b) =>
      a.name == b.name && a.key.id == b.key.id && a.parameters == b.parameters &&
        (leftCtx.typeOf a.key).alphaEquivUnder (rightCtx.typeOf b.key) [] &&
        match leftCtx.definitions a.key, rightCtx.definitions b.key with
        | some x, some y => x.alphaEquivUnder y []
        | _, _ => false

/-- Combine separately checked modules. Shared dependencies must agree, and reservations
for different modules must be disjoint even if their unused identifiers never entered scope. -/
def linkModules (left right : CheckedModules) : Except String CheckedModules := do
  for a in left.modules do
    for b in right.modules do
      if a.name == b.name then
        unless a.agrees b left.context right.context do
          throw s!"conflicting checked copies of module '{a.name}'"
      else if a.range.overlaps b.range then
        throw s!"reserved name ranges overlap for modules '{a.name}' and '{b.name}'"
  let modules :=
    left.modules.map (·.sink (leftInUnion left.scope right.scope)) ++
      (right.modules.filter fun m => (left.find? m.name).isNone).map
        (·.sink (rightInUnion left.scope right.scope))
  pure ⟨_, left.context.union right.context, modules⟩

private abbrev ParamTelescope := Telescope String (AST sig)

private abbrev NameTable (scope : Scope) := List (String × Name scope)

private def resolveModuleTerm (scope : Scope) (parameters locals imports : NameTable scope)
    (raw : Raw) : Except String (Term scope) :=
  let matchingKeys (table : NameTable scope) (text : String) :=
    table.filterMap fun (label, key) => if label == text then some key else none
  let candidates text :=
    match parameters.lookup text with
    | some parameter => [parameter]
    | none =>
      let localKeys := matchingKeys locals text
      if localKeys.isEmpty then matchingKeys imports text else localKeys
  let resolve text := do
    let key :: rest := candidates text | none
    if rest.all (·.id == key.id) then some key else none
  resolveTerm scope resolve raw fun text =>
    if (candidates text).isEmpty then s!"unbound name '{text}'" else s!"ambiguous name '{text}'"

private def sinkNames (names : NameTable source) (h : source ⊆ target) : NameTable target :=
  names.map fun (label, key) => (label, key.sink h)

private def elaborateParameters (ctx : Context scope) (names imports : NameTable scope)
    (fuel : Nat) (parameters : List Parameter) :
    Except String ((inner : Scope) × ParamTelescope scope inner) :=
  match parameters with
  | [] => pure ⟨scope, .nil⟩
  | param :: rest => do
    let type ← resolveModuleTerm scope names [] imports param.type
    (check ctx fuel type Term.univ).mapError toString
    let fresh := scope.fresh
    let outer : scope ⊆ fresh.id :: scope := List.subset_cons_self _ _
    let names := (param.name, fresh) :: sinkNames names outer
    let ⟨_, tail⟩ ← elaborateParameters (ctx.addLocal type) names (sinkNames imports outer) fuel rest
    pure ⟨_, .cons param.name type fresh.id scope.nextId_not_mem tail⟩

private def parameterContext (ctx : Context outer) (params : ParamTelescope outer inner) :
    Context inner :=
  match params with
  | .nil => ctx
  | .cons _ type id fresh rest => parameterContext (ctx.extend id fresh type) rest

private def parameterNames (params : ParamTelescope outer inner) : NameTable inner :=
  match params with
  | .nil => []
  | .cons name _ id _ rest =>
    let key : Name (id :: _) := ⟨id, by simp⟩
    (name, key.sink rest.scopeSubset) :: parameterNames rest

private def abstractDefinition (params : ParamTelescope outer inner) (type value : Term inner) :
    Term outer × Term outer :=
  match params with
  | .nil => (type, value)
  | .cons _ domain id _ rest =>
    let (type, value) := abstractDefinition rest type value
    (Term.pi domain (variableBody id type), Term.lam (variableBody id value))

private structure ModuleState (base : Scope) where
  scope : Scope
  outer : base ⊆ scope
  context : Context scope
  declarations : List (CheckedDeclaration scope)

private def ModuleState.extend (state : ModuleState base) (range : NameRange)
    (name : String) (parameters : List String) (type value : Term state.scope) :
    Except String (ModuleState base) := do
  let id := range.start + state.declarations.length
  unless id < range.stop do
    throw s!"reserved name range exhausted at declaration '{name}'"
  if fresh : id ∉ state.scope then
    let outer : state.scope ⊆ id :: state.scope := List.subset_cons_self _ _
    let key : Name (id :: state.scope) := ⟨id, by simp⟩
    pure ⟨_, fun {_} mem => outer (state.outer mem),
      state.context.extend id fresh type (some value),
      ⟨name, key, parameters⟩ :: state.declarations.map (·.sink outer)⟩
  else throw s!"declaration identifier {id} for '{name}' is already allocated"

private def importedNames (env : CheckedModules) (imports : Array String) :
    Except String (NameTable env.scope) :=
  imports.toList.flatMapM fun name => do
    let some mod := env.find? name | throw s!"missing dependency '{name}'"
    pure <| mod.declarations.flatMap fun decl =>
      [(decl.name, decl.key), (s!"{name}.{decl.name}", decl.key)]

private def checkReservation (env : CheckedModules) (name : String) (range : NameRange) :
    Except String Unit := do
  unless range.start < range.stop do
    throw s!"invalid reserved name range for module '{name}'"
  if (env.find? name).isSome then
    throw s!"duplicate module '{name}'"
  if let some other := env.modules.find? (range.overlaps ·.range) then
    throw s!"reserved name ranges overlap for modules '{name}' and '{other.name}'"

private def ModuleState.finish (env : CheckedModules) (state : ModuleState env.scope)
    (name : String) (range : NameRange) (imports : Array String) : CheckedModules :=
  let checked := ⟨name, range, imports, state.declarations.reverse⟩
  ⟨state.scope, state.context, checked :: env.modules.map (·.sink state.outer)⟩

private def runModuleCommand (state : ModuleState base) (mod : Module) (range : NameRange)
    (params : ParamTelescope base inner) (imports : NameTable base) (fuel : Nat)
    (command : Command) : Except String (ModuleState base × CommandResult) := do
  let params := (params.rename state.scope (Name.sink state.outer) (fun rename term =>
    term.rename rename)).telescope
  let ctx := parameterContext state.context params
  let namedParams := parameterNames params
  let sinkKey (key : Name state.scope) := key.sink params.scopeSubset
  let localNames := state.declarations.flatMap fun decl =>
    [(decl.name, sinkKey decl.key), (s!"{mod.name}.{decl.name}", sinkKey decl.key)]
  let imported := sinkNames imports fun {_} mem => params.scopeSubset (state.outer mem)
  let names := namedParams ++ localNames ++ imported
  let applied ← (state.declarations.filter (!·.parameters.isEmpty)).mapM fun decl => do
    let arguments ← decl.parameters.mapM fun label =>
      match namedParams.lookup label with
      | some key => pure (Term.var key)
      | none => throw s!"missing parameter '{label}' of '{decl.name}'"
    pure (decl.key.id, arguments.foldl Term.app (Term.var (sinkKey decl.key)))
  let resolve raw := do
    let term ← resolveModuleTerm _ namedParams localNames imported raw
    if applied.isEmpty then pure term
    else pure (term.substitute _ (.mapping fun key => (applied.lookup key.id).getD (.var key)))
  let display term := prettyTerm _ term fun key =>
    (names.findSome? fun (label, candidate) => if candidate.id == key.id then some label else none)
      |>.getD s!"x{key.id}"
  let define name declared rawType rawValue := do
    if state.declarations.any (·.name == name) then
      throw s!"duplicate definition '{name}'"
    let type ← resolve rawType
    let value ← resolve rawValue
    let some ⟨scope, retained⟩ := params.thinToSupport (type.freeVars ++ value.freeVars)
      | throw s!"could not thin the parameters of '{name}'"
    let some type := type.restrict scope | throw s!"could not restrict the type of '{name}'"
    let some value := value.restrict scope | throw s!"could not restrict the value of '{name}'"
    let labels := (parameterNames retained).map Prod.fst
    if let some (names : List String) := declared then
      unless names.length == labels.length && labels.all names.contains do
        throw s!"'{name}' declares over ({String.intercalate ", " names}) but uses over ({String.intercalate ", " labels})"
    let (type, value) := abstractDefinition retained type value
    (checkDefinition state.context fuel type value).mapError toString
    pure (← state.extend range name labels type value, .defined name)
  match command with
  | .define name type value => define name none type value
  | .defineOver name labels type value => define name (some labels) type value
  | .check rawTerm rawType => pure (state, ← checkQuery ctx fuel (← resolve rawTerm) (← resolve rawType) display)
  | .compute rawTerm => pure (state, ← computeQuery ctx fuel (← resolve rawTerm) display)

/-- Check a module with a caller-assigned range. Only its direct imports' exports
are visible in source. A failed command does not publish a partially checked module. -/
def checkModule (env : CheckedModules) (range : NameRange) (mod : Module) (fuel : Nat := 1024) :
    Except String (CheckedModules × Array CommandResult) := do
  checkReservation env mod.name range
  let imports ← importedNames env mod.imports
  let labels := mod.parameters.toList.map Parameter.name
  unless labels.Nodup do
    throw s!"duplicate parameter in module '{mod.name}'"
  let ⟨_, params⟩ ← elaborateParameters env.context [] imports fuel mod.parameters.toList
  let mut state : ModuleState env.scope := ⟨env.scope, fun {_} mem => mem, env.context, []⟩
  let mut results := #[]
  for i in List.finRange mod.commands.size do
    let (next, result) ← (runModuleCommand state mod range params imports fuel mod.commands[i]).mapError
      fun error => s!"module '{mod.name}', command {i.val + 1}: {error}"
    state := next
    results := results.push result
  pure (state.finish env mod.name range mod.imports, results)

/-- Separate stored global identifiers from lexical binding levels, even at the same number. -/
inductive StoredName where
  | global (id : Nat)
  | bound (level : Nat)
  deriving DecidableEq

/-- An unchecked declaration with module parameters already represented by binders. -/
structure StoredDeclaration where
  name : String
  id : Nat
  parameters : List String
  type : Syntax sig StoredName
  value : Syntax sig StoredName

private def hasParameterPrefix (type : Term typeScope) (value : Term valueScope) :
    List String → Bool
  | [] => true
  | _ :: rest =>
    match type.view, value.view with
    | .node .pi _ codomains, .node .lam _ bodies =>
      let codomain := codomains 0
      let body := bodies 0
      codomain.binder.shape == .variable && body.binder.shape == .variable &&
        hasParameterPrefix codomain.body body.body rest
    | _, _ => false

private def restoreDeclaration (state : ModuleState base) (range : NameRange)
    (importIds : List Nat) (fuel : Nat) (decl : StoredDeclaration) :
    Except String (ModuleState base) := do
  if state.declarations.any (·.name == decl.name) then
    throw s!"duplicate definition '{decl.name}'"
  unless decl.id == range.start + state.declarations.length && decl.id < range.stop do
    throw s!"invalid declaration identifier {decl.id}"
  let resolve : StoredName → Option (Name state.scope)
    | .global id =>
      if importIds.contains id || state.declarations.any (·.key.id == id) then
        Name.ofId state.scope id
      else none
    | .bound _ => none
  let restore raw := (AST.fromNamed state.scope resolve raw).mapError fun
    | .unbound (.global id) => s!"unavailable global identifier {id}"
    | .unbound (.bound level) => s!"unbound lexical level {level}"
    | .duplicateBinder _ => "duplicate name in binder pattern"
  let type ← restore decl.type
  let value ← restore decl.value
  unless decl.parameters.Nodup && hasParameterPrefix type value decl.parameters do
    throw "invalid discharged parameters"
  (checkDefinition state.context fuel type value).mapError toString
  state.extend range decl.name decl.parameters type value

/-- Recheck stored declarations in allocation order. Only direct imports and preceding
declarations can supply a free identifier. Publish the module after every check succeeds. -/
def checkStoredModule (env : CheckedModules) (name : String) (range : NameRange)
    (imports : Array String) (declarations : Array StoredDeclaration) (fuel : Nat := 1024) :
    Except String CheckedModules := do
  checkReservation env name range
  let importIds := (← importedNames env imports).map fun (_, key) => key.id
  let mut state : ModuleState env.scope := ⟨env.scope, fun {_} mem => mem, env.context, []⟩
  for decl in declarations do
    state ← (restoreDeclaration state range importIds fuel decl).mapError
      fun error => s!"module '{name}', declaration '{decl.name}': {error}"
  pure (state.finish env name range imports)

/-- A module with the identifier range it will use during checking. -/
structure PlannedModule where
  input : SourceModule
  range : NameRange

private def SourceModule.location (input : SourceModule) : String :=
  let name := s!"module '{input.mod.name}'"
  match input.source with
  | some path => s!"{name} ({path})"
  | none => name

private def importCycle (pending : Array PlannedModule) : String := Id.run do
  let base := "cyclic module imports"
  let some first := pending[0]? | return base
  let mut current := first
  let mut path := [first.input]
  for _ in pending do
    let some next := current.input.mod.imports.findSome? (fun dependency =>
      pending.find? (·.input.mod.name == dependency)) | break
    let name := next.input.mod.name
    if path.any (·.mod.name == name) then
      let cycle := path.reverse.dropWhile (·.mod.name != name) ++ [next.input]
      return s!"{base}: {String.intercalate " -> " (cycle.map SourceModule.location)}"
    current := next
    path := next.input :: path
  return base

private def planModules (inputs : Array SourceModule) : Except String (Array PlannedModule) := do
  let mut start := 0
  let mut pending := #[]
  let mut declared : List (String × SourceModule) := []
  for input in inputs do
    let name := input.mod.name
    if let some previous := declared.lookup name then
      throw s!"duplicate {input.location}, also declared as {previous.location}"
    declared := (name, input) :: declared
    let stop := start + max 1 input.mod.commands.size
    pending := pending.push ({ input, range := ⟨start, stop⟩ } : PlannedModule)
    start := stop
  for input in inputs do
    for dependency in input.mod.imports do
      unless (declared.lookup dependency).isSome do
        throw s!"{input.location} is missing dependency '{dependency}'"
  let mut ordered : Array PlannedModule := #[]
  let mut ready : List String := []
  for _ in inputs do
    let some next := pending.find? (fun entry => entry.input.mod.imports.all ready.contains)
      | throw (importCycle pending)
    let name := next.input.mod.name
    ordered := ordered.push next
    ready := name :: ready
    pending := pending.filter (·.input.mod.name != name)
  pure ordered

/-- Reserve ranges by module name, then plan the build in dependency order. -/
def planModuleProject (modules : Array SourceModule) : Except String (Array PlannedModule) :=
  planModules (modules.qsort (fun left right => left.mod.name < right.mod.name))

abbrev ModuleResults := Array (String × Array CommandResult)

/-- Check a build plan and keep both the resulting environment and command output. -/
def checkModulePlan (plan : Array PlannedModule) (fuel : Nat := 1024) :
    Except String (CheckedModules × ModuleResults) := do
  let mut env := CheckedModules.empty
  let mut results := #[]
  for entry in plan do
    let (next, output) ← (checkModule env entry.range entry.input.mod fuel).mapError fun error =>
      match entry.input.source with
      | some path => s!"{path}: {error}"
      | none => error
    env := next
    results := results.push (entry.input.mod.name, output)
  pure (env, results)

/-- Check a source project's modules with reservations independent of input file order. -/
def runModuleProject (sources : Array (String × String)) (fuel : Nat := 1024) :
    Except String (CheckedModules × ModuleResults) := do
  let modules ← Parser.parseModuleSources sources
  checkModulePlan (← planModuleProject modules) fuel

/-- Check a file's modules in dependency order, reserving a range per module in source order. -/
def runModules (modules : Array Module) (fuel : Nat := 1024) : Except String ModuleResults := do
  let plan ← planModules (modules.map fun mod => { mod })
  return (← checkModulePlan plan fuel).2

end FreeFoil.Examples.MLTT

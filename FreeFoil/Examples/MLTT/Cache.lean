import FreeFoil.Examples.MLTT.Artifact

namespace FreeFoil.Examples.MLTT

open Lean (Json ToJson FromJson toJson)
open System (FilePath)

private def encodeRaw : Raw → Json
  | .var name => .arr #[.str "var", .str name]
  | .node op terms binders bodies =>
    .arr #[.str "node", toJson op,
      .arr (Array.ofFn fun i => encodeRaw (terms i)),
      .arr (Array.ofFn fun i =>
        let binder := binders i
        .arr #[toJson binder.shape, toJson binder.names, encodeRaw (bodies i)])]

private instance : ToJson Raw := ⟨encodeRaw⟩

-- Deriving includes every expanded parameter field, including a refinement's fixed value.
deriving instance Lean.ToJson for Parameter, Command, Module
deriving instance Lean.ToJson, Lean.FromJson for CommandResult

private structure CacheEntry where
  source : Json
  fuel : Nat
  artifact : String
  results : Array CommandResult
  deriving Lean.ToJson, Lean.FromJson

private abbrev Reservations := List (String × NameRange)

private def validReservations (ranges : Reservations) : Bool :=
  let sorted := ranges.mergeSort (fun a b => a.2.start ≤ b.2.start)
  decide (ranges.map Prod.fst).Nodup &&
    sorted.all (fun (_, range) => range.start < range.stop) &&
    (sorted.zip (sorted.drop 1)).all (fun (left, right) => left.2.stop ≤ right.2.start)

private def readCacheFile [FromJson α] (path : FilePath) : IO (Option α) := do
  let contents ← try some <$> IO.FS.readFile path catch _ => pure none
  let some contents := contents | return none
  let entry : Except String α := do
    let json ← Json.parse contents
    unless (← json.getObjValAs? Nat "version") == 1 do throw "unsupported cache version"
    let data ← json.getObjVal? "data"
    unless (← json.getObjValAs? UInt64 "checksum") == hash data.compress do
      throw "invalid cache checksum"
    Lean.fromJson? data
  return entry.toOption

private def writeCacheFile [ToJson α] (directory path : FilePath) (value : α) : IO Unit := do
  let data := toJson value
  let json := Json.mkObj [("version", toJson (1 : Nat)), ("checksum", toJson (hash data.compress)),
    ("data", data)]
  let temporary := directory / s!".cache-{← IO.Process.getPID}-{← IO.monoNanosNow}.tmp"
  try
    IO.FS.writeFile temporary json.compress
    IO.FS.rename temporary path
  finally
    if ← temporary.pathExists then IO.FS.removeFile temporary

private def entryPath (directory : FilePath) (name : String) : FilePath :=
  directory / s!"module-{hash name}.json"

private def readReservations (directory : FilePath) : IO (Option Reservations) := do
  let stored ← readCacheFile (α := Reservations) (directory / "reservations.json")
  return stored.filter validReservations

/-- The first identifier above the recorded cache reservations, including unused slots. -/
def cachedReservationEnd (directory : FilePath) : IO Nat := do
  let reservations := (← readReservations directory).getD []
  return reservations.foldl (fun high (_, range) => max high range.stop) 0

private def definitionCount (mod : Module) : Nat :=
  mod.commands.countP fun
    | .define .. | .defineOver .. => true
    | .check .. | .compute .. => false

private def reserve (plan : Array PlannedModule) (reservations : Reservations) :
    Array PlannedModule × Reservations := Id.run do
  if reservations.isEmpty then
    return (plan, plan.toList.map fun entry => (entry.input.mod.name, entry.range))
  let mut next := reservations.foldl (fun high (_, range) => max high range.stop) 0
  let mut ranges := reservations
  let mut planned := #[]
  for entry in plan do
    let mod := entry.input.mod
    if let some range := ranges.lookup mod.name then
      if definitionCount mod ≤ range.stop - range.start then
        planned := planned.push { entry with range }
        continue
    let stop := next + (entry.range.stop - entry.range.start)
    let range : NameRange := ⟨next, stop⟩
    ranges := (mod.name, range) :: ranges.filter (·.1 != mod.name)
    planned := planned.push { entry with range }
    next := stop
  return (planned, ranges)

private def reuseEntry (path : FilePath) (env : CheckedModules) (entry : PlannedModule)
    (source : Json) (fuel : Nat) : IO (Option (CheckedModules × Array CommandResult)) := do
  let some cached ← readCacheFile (α := CacheEntry) path | return none
  if cached.fuel != fuel || cached.source != source then return none
  let .ok artifact := decodeArtifact cached.artifact | return none
  let mod := entry.input.mod
  let payload := artifact.payload
  if payload.name != mod.name || payload.range != entry.range || payload.imports != mod.imports ||
      payload.declarations.size != definitionCount mod || cached.results.size != mod.commands.size then
    return none
  let .ok checked := loadArtifact env artifact fuel | return none
  return some (checked, cached.results)

/-- The checked environment and replayed command output of a cached module project. -/
structure CachedModuleProject where
  environment : CheckedModules
  results : ModuleResults
  reused : Array String

private def checkWithCache (directory : FilePath) (plan : Array PlannedModule) (fuel : Nat) :
    ExceptT String IO CachedModuleProject := do
  let index := directory / "reservations.json"
  let previous := (← readReservations directory).getD []
  let (plan, reservations) := reserve plan previous
  let mut environment := CheckedModules.empty
  let mut results := #[]
  let mut reused := #[]
  let mut updates : Array (FilePath × CacheEntry) := #[]
  for entry in plan do
    let mod := entry.input.mod
    let source := toJson mod
    let path := entryPath directory mod.name
    if let some (checked, output) ← reuseEntry path environment entry source fuel then
      environment := checked
      results := results.push (mod.name, output)
      reused := reused.push mod.name
    else
      let (checked, output) ← liftExcept ((checkModule environment entry.range mod fuel).mapError
        fun error => match entry.input.source with
          | some path => s!"{path}: {error}"
          | none => error)
      let artifact ← liftExcept (makeArtifact checked mod.name)
      environment := checked
      results := results.push (mod.name, output)
      updates := updates.push (path, ⟨source, fuel, encodeArtifact artifact, output⟩)
  -- Publish only after checking the whole project. An interrupted write leaves the
  -- old entry intact, and a mismatched entry is rechecked on the next build.
  if reservations != previous then writeCacheFile directory index reservations
  for (path, cached) in updates do
    writeCacheFile directory path cached
  return ⟨environment, results, reused⟩

/-- Check a module project with persistent identifier ranges and revalidated artifacts.
Cached command results are replayed when a module is reused. -/
def runCachedModuleProject (directory : FilePath) (sources : Array (String × String))
    (fuel : Nat := 1024) : IO (Except String CachedModuleProject) := do
  let plan ← match Parser.parseModuleSources sources >>= planModuleProject with
    | .ok plan => pure plan
    | .error error => return .error error
  IO.FS.createDirAll directory
  let lock ← IO.FS.Handle.mk (directory / "cache.lock") .append
  lock.lock
  try
    (checkWithCache directory plan fuel).run
  finally
    lock.unlock

private partial def loadCachedDependencies (directory : FilePath) (reservations : Reservations)
    (fuel : Nat) (env : CheckedModules) (name : String) (visiting : List String) :
    ExceptT String IO CheckedModules := do
  if (env.find? name).isSome then return env
  if visiting.contains name then
    throw s!"cyclic cached module imports: {String.intercalate " -> " (name :: visiting).reverse}"
  let path := entryPath directory name
  let some cached ← readCacheFile (α := CacheEntry) path
    | throw s!"missing or invalid cached module '{name}' at '{path}'"
  let artifact ← liftExcept ((decodeArtifact cached.artifact).mapError fun error =>
    s!"cached module '{name}' at '{path}': {error}")
  unless artifact.payload.name == name do
    throw s!"cached module '{name}' at '{path}' contains '{artifact.payload.name}'"
  unless reservations.lookup name == some artifact.payload.range do
    throw s!"cached module '{name}' at '{path}' does not match its recorded reservation"
  let mut checked := env
  for dependency in artifact.payload.imports do
    checked ← loadCachedDependencies directory reservations fuel checked dependency (name :: visiting)
  liftExcept ((loadArtifact checked artifact fuel).mapError fun error =>
    s!"cached module '{name}' at '{path}': {error}")

/-- Restore a cached module and any missing imports in dependency order. The builder's
lock keeps reservations and entries consistent throughout the load. -/
private def loadCachedModule (directory : FilePath) (env : CheckedModules) (name : String)
    (fuel : Nat) : IO (Except String CheckedModules) := do
  let load : ExceptT String IO CheckedModules := do
    let some reservations ← readReservations directory
      | throw s!"missing or invalid cache reservation index at '{directory / "reservations.json"}'"
    loadCachedDependencies directory reservations fuel env name []
  let lockPath := directory / "cache.lock"
  if ← lockPath.pathExists then
    let lock ← IO.FS.Handle.mk lockPath .read
    lock.lock (exclusive := false)
    try load.run finally lock.unlock
  else load.run

/-- Bring a module's own exports into scope. If needed, validate its cached artifacts before
publishing any additions to the session. -/
def ReplSession.importModule (session : ReplSession) (name : String)
    (cache : Option FilePath := none) (fuel : Nat := 1024) : IO (Except String ReplSession) := do
  if (session.environment.find? name).isSome then
    return session.addImport session.environment name
  let some directory := cache | return .error s!"unknown module '{name}'"
  try
    return (← loadCachedModule directory session.environment name fuel).bind fun loaded =>
      session.addImport loaded name
  catch error =>
    return .error (toString error)

end FreeFoil.Examples.MLTT

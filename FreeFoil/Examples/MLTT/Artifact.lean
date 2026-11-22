import FreeFoil.Examples.MLTT.Module
import Lean.Data.Json
import Lean.Elab.Deriving.FromToJson
import Std.Data.HashSet

namespace FreeFoil.Examples.MLTT

open Lean (Json toJson fromJson?)

deriving instance Lean.ToJson, Lean.FromJson for Op, Pattern, NameRange

/-- The serialized type and value are unchecked until the artifact is loaded. -/
structure ArtifactDeclaration where
  name : String
  id : Nat
  parameters : List String
  type : Json
  value : Json
  deriving Lean.ToJson, Lean.FromJson

structure ArtifactPayload where
  name : String
  range : NameRange
  imports : Array String
  declarations : Array ArtifactDeclaration
  deriving Lean.ToJson, Lean.FromJson

structure ArtifactDependency where
  name : String
  checksum : UInt64
  deriving BEq, Lean.ToJson, Lean.FromJson

structure ModuleArtifact where
  payload : ArtifactPayload
  dependencies : Array ArtifactDependency
  deriving Lean.ToJson, Lean.FromJson

private def encodeTerm : Lexical sig → Json
  | .free id => .arr #[.str "free", toJson id]
  | .bound level => .arr #[.str "bound", toJson level]
  | .node op terms shapes bodies => .arr #[
      .str "node",
      toJson op,
      .arr (Array.ofFn fun i => encodeTerm (terms i)),
      .arr (Array.ofFn fun i => .arr #[toJson (shapes i), encodeTerm (bodies i)])]

private partial def decodeTerm (depth : Nat) (json : Json) : Except String (Syntax sig StoredName) := do
  match ← json.getArr? with
  | #[.str "free", id] => return .var (.global (← id.getNat?))
  | #[.str "bound", level] => return .var (.bound (← level.getNat?))
  | #[.str "node", op, terms, children] =>
    let op : Op ← fromJson? op
    let terms ← terms.getArr?
    let children ← children.getArr?
    let terms : Vector Json (sig.terms op) ←
      if h : terms.size = sig.terms op then pure ⟨terms, h⟩ else throw "wrong term arity"
    let children : Vector Json (sig.scopes op) ←
      if h : children.size = sig.scopes op then pure ⟨children, h⟩ else throw "wrong scoped child arity"
    let terms ← terms.mapM (decodeTerm depth)
    let children ← children.mapM fun child => do
      let #[shape, body] ← child.getArr? | throw "malformed scoped child"
      let shape : Pattern ← fromJson? shape
      let arity := sig.binders shape
      let names := (List.range arity).reverse.map fun i => StoredName.bound (depth + i)
      let binder : Binder sig StoredName := ⟨shape, names, by simp [names, arity]⟩
      pure (binder, ← decodeTerm (depth + arity) body)
    return .node op terms.get (fun i => (children.get i).1) (fun i => (children.get i).2)
  | _ => throw "malformed term"

private def modulePayload (env : CheckedModules) (mod : CheckedModule env.scope) :
    Except String ArtifactPayload := do
  let declarations ← mod.declarations.toArray.mapM fun decl => do
    let some value := env.context.definitions decl.key
      | throw s!"missing checked definition '{decl.name}' in module '{mod.name}'"
    let store (term : Term env.scope) :=
      encodeTerm (Lexical.interpret term.syntaxTree 0 Lexical.freeAssignment)
    pure ⟨decl.name, decl.key.id, decl.parameters, store (env.context.typeOf decl.key), store value⟩
  pure ⟨mod.name, mod.range, mod.imports, declarations⟩

-- FNV-1a over the canonical payload, for detecting changes to checked dependencies.
private def dependencyChecksum (payload : ArtifactPayload) : UInt64 :=
  (toJson payload).compress.toUTF8.foldl
    (fun hash byte => (hash ^^^ byte.toUInt64) * 0x100000001b3) 0xcbf29ce484222325

private def dependencyManifest (env : CheckedModules) (imports : Array String) :
    Except String (Array ArtifactDependency) := do
  let mut pending := imports.toList
  let mut seen : Std.HashSet String := {}
  let mut result := #[]
  while let name :: rest := pending do
    pending := rest
    if !seen.contains name then
      let some mod := env.find? name | throw s!"missing dependency '{name}'"
      seen := seen.insert name
      pending := mod.imports.toList ++ pending
      result := result.push ⟨name, dependencyChecksum (← modulePayload env mod)⟩
  pure (result.qsort (fun a b => a.name < b.name))

/-- Store a checked module at its existing reservation and record the identities of its dependencies. -/
def makeArtifact (env : CheckedModules) (name : String) : Except String ModuleArtifact := do
  let some mod := env.find? name | throw s!"unknown checked module '{name}'"
  pure ⟨← modulePayload env mod, ← dependencyManifest env mod.imports⟩

def encodeArtifact (artifact : ModuleArtifact) : String :=
  (Json.mkObj [("format", .str "free-foil-mltt"), ("version", toJson (1 : Nat)),
    ("module", toJson artifact)]).compress

/-- Decode the versioned envelope and its payload. Loading separately validates the terms,
dependencies and allocation against the checked environment. -/
def decodeArtifact (source : String) : Except String ModuleArtifact := do
  let json ← Json.parse source
  unless (← json.getObjValAs? String "format") == "free-foil-mltt" do
    throw "invalid MLTT artifact format"
  unless (← json.getObjValAs? Nat "version") == 1 do
    throw "unsupported MLTT artifact version"
  json.getObjValAs? ModuleArtifact "module"

/-- Reconstruct one checked module over its previously checked imports. -/
def loadArtifact (env : CheckedModules) (artifact : ModuleArtifact) (fuel : Nat := 1024) :
    Except String CheckedModules := do
  let payload := artifact.payload
  let dependencies ← dependencyManifest env payload.imports
  unless artifact.dependencies == dependencies do
    throw s!"dependency manifest does not match the checked imports of '{payload.name}'"
  let declarations ← payload.declarations.mapM fun decl => do
    let decode field term := (decodeTerm 0 term).mapError fun error =>
      s!"module '{payload.name}', declaration '{decl.name}', {field}: {error}"
    pure ⟨decl.name, decl.id, decl.parameters, ← decode "type" decl.type, ← decode "value" decl.value⟩
  checkStoredModule env payload.name payload.range payload.imports declarations fuel

end FreeFoil.Examples.MLTT

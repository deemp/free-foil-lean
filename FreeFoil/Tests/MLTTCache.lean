import FreeFoil.Examples.MLTT.Cache

namespace FreeFoil.Tests.MLTTCache

open Examples.MLTT
open System (FilePath)

private def verify (message : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError message)

private def expectOk (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def provider (carrier binder : String) : String :=
  s!"module Provider\ndef carrier : 𝕌 := {carrier}\n\
    def ident : Π (x : 𝟙) → 𝟙 := λ {binder} ⇒ {binder}\ncompute carrier"

private def sources (carrier binder : String) : Array (String × String) :=
  #[("provider.mltt", provider carrier binder),
    ("client.mltt", "module Client\nimport Provider\ndef alias : 𝕌 := carrier\ncompute alias")]

private def build (cache : FilePath) (files : Array (String × String)) : IO CachedModuleProject := do
  expectOk (← runCachedModuleProject cache files)

private def reservation (env : CheckedModules) (name : String) : IO (NameRange × List Nat) := do
  let some mod := env.find? name | throw (IO.userError s!"missing checked module {name}")
  pure (mod.range, mod.declarations.map (·.key.id))

private def cacheTests : IO Unit := IO.FS.withTempDir fun directory => do
  let cache := directory / "cache"
  let original := sources "𝟙" "x"
  let cold ← build cache original
  verify "cold MLTT build reported a cache hit" cold.reused.isEmpty
  let warm ← build cache original.reverse
  verify "warm MLTT build did not reuse every module and its command output"
    (warm.reused == #["Provider", "Client"] && warm.results == cold.results)

  let expanded := original.push ("aardvark.mltt", "module Aardvark\ndef extra : 𝕌 := 𝟙")
  let incremental ← build cache expanded
  verify "adding an unrelated module invalidated cached clients"
    (incremental.reused == #["Provider", "Client"])
  for name in ["Provider", "Client"] do
    verify s!"adding an unrelated module changed the identifier range of {name}"
      ((← reservation cold.environment name) == (← reservation incremental.environment name))

  let equivalent ← build cache (sources "𝟙" "renamed")
  verify "a binder rename did not rebuild only the edited provider"
    (equivalent.reused == #["Client"] && equivalent.results == cold.results)
  let changedSources := sources "𝕌" "renamed"
  let changed ← build cache changedSources
  verify "a checked dependency change did not invalidate the dependent module"
    (changed.reused.isEmpty && changed.results ==
      #[("Provider", #[.defined "carrier", .defined "ident", .computed "𝕌"]),
        ("Client", #[.defined "alias", .computed "𝕌"])])

  let providerEntry := cache / s!"module-{hash "Provider"}.json"
  IO.FS.writeFile providerEntry "corrupt"
  let recovered ← build cache changedSources
  verify "an invalid artifact did not fall back to source checking"
    (recovered.reused == #["Client"] && recovered.results == changed.results)
  verify "corrupting an artifact changed its module's reservation"
    ((← reservation recovered.environment "Provider") == (← reservation changed.environment "Provider"))
  verify "artifact recovery did not repair the cache"
    ((← build cache changedSources).reused == #["Provider", "Client"])

  let before ← IO.FS.readFile providerEntry
  let broken := (sources "𝟙" "other").set! 1 ("client.mltt", "module Client\nimport Provider\ncompute absent")
  match ← runCachedModuleProject cache broken with
  | .ok _ => throw (IO.userError "an invalid MLTT project succeeded against cached artifacts")
  | .error error =>
    verify "an invalid cache build lost its source diagnostic"
      (error.contains "client.mltt" && error.contains "absent")
  verify "a failed project published a replacement artifact"
    ((← IO.FS.readFile providerEntry) == before)

private def expandedHeaderCacheTest : IO Unit := IO.FS.withTempDir fun directory => do
  let client := ("client.mltt", "module Client include Carrier\ndef alias : 𝕌 := 𝟙")
  let _ ← build directory #[("header.mltt", "telescope Carrier (A : 𝕌)"), client]
  let changed ← build directory #[("header.mltt", "telescope Carrier (A : 𝟙)"), client]
  verify "changing an included telescope did not rebuild its client" changed.reused.isEmpty
  let header := ("header.mltt", "telescope Carrier (A : 𝕌)")
  let refined (value : String) := ("client.mltt",
    "module Client include Carrier / {A := " ++ value ++ "}\ndef alias : 𝕌 := A\ncompute alias")
  let _ ← build directory #[header, refined "𝟙"]
  let changed ← build directory #[header, refined "𝕌"]
  verify "changing a fixed field did not rebuild its client"
    (changed.reused.isEmpty && changed.results == #[("Client", #[.defined "alias", .computed "𝕌"])])

private def cliTests : IO Unit := IO.FS.withTempDir fun directory => do
  let executable := if System.Platform.isWindows then "mltt.exe" else "mltt"
  let mltt := (← IO.appDir) / executable
  let cache := directory / "cache"
  let files := sources "𝟙" "x"
  for (name, contents) in files do
    IO.FS.writeFile (directory / name) contents
  let run (files : Array (String × String)) := IO.Process.output {
    cmd := mltt.toString
    args := #["--cache", cache.toString] ++ files.map (fun (path, _) => (directory / path).toString) }
  let cold ← run files
  let warm ← run files.reverse
  let expected := "module Provider\n  ✓ defined carrier\n  ✓ defined ident\n  ↦ 𝟙\n\
    module Client\n  ✓ defined alias\n  ↦ 𝟙\n"
  for output in [cold, warm] do
    verify s!"unexpected cached MLTT CLI output: {output.stdout}{output.stderr}"
      (output.exitCode == 0 && output.stdout.replace "\r\n" "\n" == expected && output.stderr.isEmpty)

def run : IO Unit := do
  cacheTests
  expandedHeaderCacheTest
  cliTests

end FreeFoil.Tests.MLTTCache

import FreeFoil.Examples.MLTT.Cache

open FreeFoil.Examples.MLTT

private def printModuleResults (results : ModuleResults) : IO Unit := do
  for (name, commands) in results do
    IO.println s!"module {name}"
    for command in commands do
      IO.println s!"  {command}"

private def run (source input : String) (parallel : Bool := false) : IO UInt32 := do
  let parsed ← match Parser.parseInput input with
    | .ok input => pure input
    | .error error =>
      IO.eprintln s!"{source}: parse error at {error}"
      return 1
  match parsed with
  | .standalone program =>
    if let some name := program.moduleName then
      IO.println s!"module {name}"
    let results := runProgram program
    let mut exitCode : UInt32 := 0
    for i in List.finRange results.size do
      match results[i] with
      | .ok output => IO.println s!"  {output}"
      | .error error =>
        IO.eprintln s!"{source}: command {i.val + 1}: {error}"
        exitCode := 1
    return exitCode
  | .modules modules =>
    let result ← if parallel then runModulesParallel modules else pure (runModules modules)
    match result with
    | .ok results =>
      printModuleResults results
      return 0
    | .error error =>
      IO.eprintln s!"{source}: {error}"
      return 1

private def runProject (paths : List String) (cache : Option System.FilePath := none)
    (parallel : Bool := false) : IO UInt32 := do
  let sources ← paths.toArray.mapM fun (path : String) => do
    pure (path, ← IO.FS.readFile path)
  let result ← match cache with
    | some directory => pure ((← runCachedModuleProject directory sources).map (·.results))
    | none =>
      let checked ← if parallel then runModuleProjectParallel sources else pure (runModuleProject sources)
      pure (checked.map Prod.snd)
  match result with
  | .ok results =>
    printModuleResults results
    return 0
  | .error error =>
    IO.eprintln error
    return 1

private def usage : IO UInt32 := do
  IO.eprintln "usage: mltt [file ... | -] | mltt --parallel (file ... | -) | mltt --cache directory file ..."
  return 2

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["--parallel", "-"] => run "stdin" (← (← IO.getStdin).readToEnd) (parallel := true)
    | "--parallel" :: paths =>
      match paths with
      | [] => usage
      | [path] =>
        if path == "--cache" then usage else run path (← IO.FS.readFile path) (parallel := true)
      | _ =>
        if paths.contains "-" || paths.contains "--cache" then usage
        else runProject paths (parallel := true)
    | "--cache" :: directory :: paths =>
      if paths.isEmpty || paths.contains "-" || paths.contains "--parallel" then usage
      else runProject paths (some directory)
    | ["--cache"] => usage
    | [] | ["-"] => run "stdin" (← (← IO.getStdin).readToEnd)
    | [path] => run path (← IO.FS.readFile path)
    | paths => if paths.contains "-" then usage else runProject paths
  catch error =>
    IO.eprintln s!"mltt: {error}"
    return 1

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

private def runRepl (environment : CheckedModules) (cache : Option System.FilePath) : IO UInt32 := do
  let reservedEnd := (← cache.mapM cachedReservationEnd).getD 0
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let prompt := (← stdin.isTty) && (← stdout.isTty)
  let mut session := ReplSession.start environment
  repeat
    if prompt then stdout.putStr "mltt> "
    stdout.flush
    let line ← stdin.getLine
    if line.isEmpty then
      if prompt then stdout.putStrLn ""
      return 0
    match Parser.parseSessionLine line with
    | .error error => IO.eprintln s!"repl: parse error at {error}"
    | .ok none => pure ()
    | .ok (some (.importModule name)) =>
      match ← session.importModule name cache with
      | .error error => IO.eprintln s!"repl: import '{name}': {error}"
      | .ok next =>
        session := next
        stdout.putStrLn s!"✓ imported {name}"
    | .ok (some (.command command)) =>
      match session.step command reservedEnd with
      | .error error => IO.eprintln s!"repl: {error}"
      | .ok (next, result) =>
        session := next
        stdout.putStrLn (toString result)

private def runProject (paths : List String) (cache : Option System.FilePath := none)
    (parallel repl : Bool := false) : IO UInt32 := do
  let sources ← paths.toArray.mapM fun (path : String) => do
    pure (path, ← IO.FS.readFile path)
  let result ← match cache with
    | some directory => pure ((← runCachedModuleProject directory sources).map fun project =>
        (project.environment, project.results))
    | none =>
      if parallel then runModuleProjectParallel sources else pure (runModuleProject sources)
  match result with
  | .ok (environment, results) =>
    printModuleResults results
    if repl then runRepl environment cache else return 0
  | .error error =>
    IO.eprintln error
    return 1

private def usage : IO UInt32 := do
  IO.eprintln "usage: mltt [file ... | -] | mltt --parallel (file ... | -) | mltt --cache directory file ..."
  IO.eprintln "       mltt --repl [--cache directory | --parallel] [file ...]"
  return 2

private def runReplProject (paths : List String) (cache : Option System.FilePath := none)
    (parallel : Bool := false) : IO UInt32 := do
  if paths.any (fun path => path == "-" || path.startsWith "--") then usage
  else if paths.isEmpty then runRepl CheckedModules.empty cache
  else runProject paths cache parallel (repl := true)

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | "--repl" :: "--cache" :: directory :: paths
    | "--cache" :: directory :: "--repl" :: paths =>
      runReplProject paths (some directory)
    | "--repl" :: "--parallel" :: paths
    | "--parallel" :: "--repl" :: paths => runReplProject paths (parallel := true)
    | "--repl" :: paths => runReplProject paths
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

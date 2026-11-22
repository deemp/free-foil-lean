import FreeFoil.Examples.MLTT.Module

open FreeFoil.Examples.MLTT

private def printModuleResults (results : ModuleResults) : IO Unit := do
  for (name, commands) in results do
    IO.println s!"module {name}"
    for command in commands do
      IO.println s!"  {command}"

private def run (source input : String) : IO UInt32 := do
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
    match runModules modules with
    | .ok results =>
      printModuleResults results
      return 0
    | .error error =>
      IO.eprintln s!"{source}: {error}"
      return 1

private def runProject (paths : List String) : IO UInt32 := do
  let sources ← paths.toArray.mapM fun (path : String) => do
    pure (path, ← IO.FS.readFile path)
  match runModuleProject sources with
  | .ok (_, results) =>
    printModuleResults results
    return 0
  | .error error =>
    IO.eprintln error
    return 1

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | [] | ["-"] => run "stdin" (← (← IO.getStdin).readToEnd)
    | [path] => run path (← IO.FS.readFile path)
    | paths =>
      if paths.contains "-" then
        IO.eprintln "usage: mltt [file ... | -]"
        return 2
      runProject paths
  catch error =>
    IO.eprintln s!"mltt: {error}"
    return 1

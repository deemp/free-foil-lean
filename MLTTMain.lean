import FreeFoil.Examples.MLTT.Program

open FreeFoil.Examples.MLTT

private def run (source input : String) : IO UInt32 := do
  let program ← match Parser.parseProgram input with
    | .ok program => pure program
    | .error error =>
      IO.eprintln s!"{source}: parse error at {error}"
      return 1
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

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | [] | ["-"] => run "stdin" (← (← IO.getStdin).readToEnd)
    | [path] => run path (← IO.FS.readFile path)
    | _ =>
      IO.eprintln "usage: mltt [file|-]"
      return 2
  catch error =>
    IO.eprintln s!"mltt: {error}"
    return 1

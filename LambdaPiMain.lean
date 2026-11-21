import FreeFoil.Examples.LambdaPi.Program

open FreeFoil.Examples.LambdaPi

private def run (source : String) (input : String) : IO UInt32 := do
  let commands ← match Parser.parseProgram input with
    | .ok commands => pure commands
    | .error message =>
      IO.eprintln s!"{source}: parse error at {message}"
      return 1
  let mut exitCode : UInt32 := 0
  for i in List.finRange commands.size do
    match interpret 1024 commands[i] with
    | .ok output => IO.println output
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
      IO.eprintln "usage: lambdaPi [file|-]"
      return 2
  catch error =>
    IO.eprintln s!"lambdaPi: {error}"
    return 1

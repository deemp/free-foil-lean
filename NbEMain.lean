import FreeFoil.Examples.NbEDemos.Program

open FreeFoil.Examples.NbEDemos

def main (args : List String) : IO UInt32 := do
  let usage := "usage: nbe <lambda-pi|booleans|let|pairs|naturals> '<term>' [free-names...]"
  let demo :: source :: freeNames := args | IO.eprintln usage *> pure 2
  let norm := fun {sig : FreeFoil.Signature} (language : Demo sig) =>
    language.normalize 1024 source freeNames
  let result ← match demo with
    | "lambda-pi" => pure (norm lambdaPi)
    | "booleans" => pure (norm booleans)
    | "let" => pure (norm lambdaLet)
    | "pairs" => pure (norm pairs)
    | "naturals" => pure (norm naturals)
    | _ => IO.eprintln usage *> pure (.error s!"unknown demo '{demo}'")
  match result with
  | .ok output => IO.println output *> pure 0
  | .error error => IO.eprintln s!"nbe: {error}" *> pure 1

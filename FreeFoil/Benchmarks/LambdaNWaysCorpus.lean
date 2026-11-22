import FreeFoil.Examples.LambdaPi
import FreeFoil.Examples.TermParser

namespace FreeFoil.Benchmarks.LambdaNWaysCorpus

open FreeFoil.Examples.LambdaPi
open FreeFoil.Examples.TermParser
open Std.Internal.Parsec
open Std.Internal.Parsec.String (Parser)

private def identifier : Parser String := Examples.TermParser.identifier ["let", "in"]

private partial def term : Parser Raw :=
  lambda <|> letBlock <|> applications Raw.app atom
where
  lambda := do
    symbol "\\"
    let name ← identifier
    symbol "."
    return Raw.lam name (← term)
  letBlock := do
    keyword "let"
    let first ← binding
    let rest ← many (symbol ";" *> binding)
    keyword "in"
    let body ← term
    return bind first (rest.foldr bind body)
  binding := do
    let name ← identifier
    symbol "="
    return (name, ← term)
  bind (entry : String × Raw) (body : Raw) : Raw :=
    Raw.app (Raw.lam entry.1 body) entry.2
  atom := (Raw.var <$> identifier) <|> parenthesized term

structure Fixture where
  location : String
  raw : Raw

def Fixture.close (fixture : Fixture) : Except String (Term []) :=
  (AST.fromClosed fixture.raw).mapError (fun error => s!"{fixture.location}: {reprStr error}")

private def parse (location source : String) : IO Fixture := do
  let raw ← IO.ofExcept <| ((trivia *> term <* eof).run source).mapError
    (fun error => s!"{location}: {error}")
  return ⟨location, raw⟩

def readTerm (path : System.FilePath) : IO Fixture := do
  parse (toString path) (← IO.FS.readFile path)

def readGroup (path : System.FilePath) : IO (Array Fixture) := do
  let lines ← IO.FS.lines path
  let mut terms := #[]
  for (line, index) in lines.zipIdx do
    let line := line.trimAscii.toString
    unless line.isEmpty || line.startsWith "--" do
      terms := terms.push (← parse s!"{path}:{index + 1}" line)
  if terms.isEmpty then throw (IO.userError s!"{path}: no lambda terms")
  return terms

end FreeFoil.Benchmarks.LambdaNWaysCorpus

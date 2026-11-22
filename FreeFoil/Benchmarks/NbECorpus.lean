import FreeFoil.Examples.LambdaPi
import FreeFoil.Examples.TermParser

namespace FreeFoil.Benchmarks.NbECorpus

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

private def readTerm (whereFrom source : String) : IO (Term []) := do
  let raw ← IO.ofExcept <| ((trivia *> term <* eof).run source).mapError
    (fun error => s!"{whereFrom}: {error}")
  IO.ofExcept <| (AST.fromClosed raw).mapError (fun error => s!"{whereFrom}: {reprStr error}")

private def readGroup (path : System.FilePath) : IO (Array (Term [])) := do
  let lines ← IO.FS.lines path
  let mut terms := #[]
  for (line, index) in lines.zipIdx do
    let line := line.trimAscii.toString
    unless line.isEmpty || line.startsWith "--" do
      terms := terms.push (← readTerm s!"{path}:{index + 1}" line)
  if terms.isEmpty then throw (IO.userError s!"{path}: no lambda terms")
  return terms

/-- Read the three untyped lambda-n-ways fixtures used by the pinned upstream harness. -/
def load (dir : System.FilePath) : IO (Array (String × Array (Term []))) := do
  let factorial := dir / "lennart.lam"
  let factorialTerm ← readTerm (toString factorial) (← IO.FS.readFile factorial)
  let random15 ← readGroup (dir / "random15.lam")
  let random20 ← readGroup (dir / "random20.lam")
  return #[("factorial", #[factorialTerm]), ("random15", random15), ("random20", random20)]

end FreeFoil.Benchmarks.NbECorpus

import FreeFoil.Examples.DependentTypes.Elaborate
import FreeFoil.Examples.TermParser

namespace FreeFoil.Examples.DependentTypes

open Std.Internal.Parsec
open Std.Internal.Parsec.String (Parser digits)
open FreeFoil.Examples.TermParser

private partial def termParser : Parser Surface.NamedTerm :=
  lambda <|> typeFormer <|> application
where
  name : Parser String := identifier ["U", "Unit", "tt", "first", "second"]
  binder : Parser (String × Surface.NamedTerm) := parenthesized do
    let name ← name
    symbol ":"
    pure (name, ← termParser)
  bind name (body : Surface.NamedTerm) : BoundSyntax Unit arity Surface.NamedTerm :=
    ⟨(), [name], rfl, body⟩
  lambda : Parser Surface.NamedTerm := do
    symbol "\\"
    let (name, domain) ← binder
    symbol "."
    pure (.lam domain (bind name (← termParser)))
  typeFormer : Parser Surface.NamedTerm := do
    let (name, domain, op) ← attempt do
      let (name, domain) ← binder
      let op ← (symbol "->" *> pure Surface.NamedTerm.pi) <|>
        (symbol "*" *> pure Surface.NamedTerm.sigma)
      pure (name, domain, op)
    pure (op domain (bind name (← termParser)))
  application : Parser Surface.NamedTerm := do
    let head ← (keyword "first" *> (Surface.NamedTerm.first <$> atom)) <|>
      (keyword "second" *> (Surface.NamedTerm.second <$> atom)) <|> atom
    let args ← many atom
    pure (args.foldl Surface.NamedTerm.app head)
  atom : Parser Surface.NamedTerm :=
    (keyword "U" *> (Surface.NamedTerm.universe <$> (digits <* trivia))) <|>
    (keyword "Unit" *> pure .unitType) <|> (keyword "tt" *> pure .unitVal) <|>
    (.var <$> name) <|> parenthesized do
      let first ← termParser
      if (← optional (symbol ",")).isSome then
        pure (.pair first (← termParser))
      else pure first

def parse (source : String) : Except String Surface.NamedTerm :=
  (trivia *> termParser <* eof).run source

private def resolveError : ResolveError String → String
  | .unbound name => s!"unbound name '{name}'"
  | .duplicateBinder names => s!"duplicate names in binder ({String.intercalate ", " names})"

/-- Parse and scope-check a closed term in the upstream grammar. -/
def parseClosed (source : String) : Except String (Surface.Term []) := do
  let term ← parse source
  term.resolveClosed.mapError resolveError

/-- Elaborate a named term and its expected type, both in the empty context. -/
def elaborate (fuel : Nat) (source expected : String) :
    Except String (Elaborated [] × Elaborated []) := do
  let term ← parseClosed source
  let type ← parseClosed expected
  (elaborateScoped .empty fuel term type).mapError toString

/-- Elaborate a named term and render its full normal form. -/
def normalize (fuel : Nat) (source expected : String) : Except String String := do
  let (term, _) ← elaborate fuel source expected
  let normal ← (nf .empty fuel term).mapError fun error => toString (TypeError.evaluation error)
  pure (normal.pretty fun name => nomatch name.property)

end FreeFoil.Examples.DependentTypes

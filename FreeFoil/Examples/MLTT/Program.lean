import FreeFoil.Examples.MLTT.Typecheck
import Std.Internal.Parsec.String

namespace FreeFoil.Examples.MLTT

inductive Command where
  | define (name : String) (type value : Raw)
  | defineOver (name : String) (parameters : List String) (type value : Raw)
  | check (term type : Raw)
  | compute (term : Raw)

structure Program where
  moduleName : Option String
  commands : Array Command

structure Parameter where
  name : String
  type : Raw

structure Module where
  name : String
  parameters : Array Parameter
  imports : Array String
  commands : Array Command

inductive Input where
  | standalone (program : Program)
  | modules (modules : Array Module)

namespace Parser

open Std.Internal.Parsec
open Std.Internal.Parsec.String (Parser skipString ws)

private partial def skipBlockComment : Parser Unit :=
  skipString "-}" <|> (skipString "{-" *> skipBlockComment *> skipBlockComment) <|>
    (any *> skipBlockComment)

private def trivia : Parser Unit := do
  ws
  let _ ← many do
    (skipString "--" *> many (satisfy (· != '\n')) *> pure ()) <|>
      (skipString "{-" *> skipBlockComment)
    ws

private def symbol (text : String) : Parser Unit :=
  skipString text *> trivia

private def isLetter (c : Char) : Bool :=
  c.isAlpha || (c >= 'À' && c <= 'ÿ' && c != '×' && c != '÷')

private def isIdentRest (c : Char) : Bool :=
  isLetter c || c.isDigit || c == '_' || c == '\'' || c == '.'

private def keyword (text : String) : Parser Unit :=
  attempt (skipString text *> notFollowedBy (satisfy isIdentRest)) *> trivia

private def identifier : Parser String := do
  let name ← attempt do
    let first ← satisfy isLetter
    let rest ← many (satisfy isIdentRest)
    let name := String.ofList (first :: rest.toList)
    if ["module", "telescope", "include", "import", "namespace", "where", "open", "over",
        "private", "def", "check", "compute", "let", "in", "tt", "Id", "refl", "J"].contains name then
      fail "expected an identifier"
    else
      pure name
  trivia
  pure name

private partial def pattern : Parser (Binder sig String) :=
  (symbol "_" *> pure Raw.wildcard) <|> (Raw.varPattern <$> identifier) <|> do
    symbol "("
    let left ← pattern
    symbol ","
    let right ← pattern
    symbol ")"
    pure (Raw.pairPattern left right)

private partial def term : Parser NamedTerm :=
  lambda <|> quantified "Π" "→" NamedTerm.pi <|> quantified "Σ" "×" NamedTerm.sigma <|>
    letTerm <|> application
where
  lambda : Parser NamedTerm := do
    symbol "λ"
    let first ← pattern
    let rest ← many pattern
    symbol "⇒"
    let body ← term
    pure ((#[first] ++ rest).foldr (fun binder body => .lam (BoundSyntax.ofBinder binder body)) body)
  quantified (quantifier separator : String)
      (make : NamedTerm → BoundSyntax Pattern Pattern.binders NamedTerm → NamedTerm) :
      Parser NamedTerm := do
    symbol quantifier
    symbol "("
    let first ← pattern
    let rest ← if quantifier == "Π" then many pattern else pure #[]
    symbol ":"
    let domain ← term
    symbol ")"
    symbol separator
    let body ← term
    pure ((#[first] ++ rest).foldr (fun binder body => make domain (BoundSyntax.ofBinder binder body)) body)
  letTerm : Parser NamedTerm := do
    keyword "let"
    let binder ← pattern
    symbol "="
    let value ← term
    keyword "in"
    pure (.letIn value (BoundSyntax.ofBinder binder (← term)))
  triple (name : String) (make : NamedTerm → NamedTerm → NamedTerm → NamedTerm) : Parser NamedTerm := do
    keyword name
    symbol "("
    let first ← term
    symbol ","
    let second ← term
    symbol ","
    let third ← term
    symbol ")"
    pure (make first second third)
  reflTerm : Parser NamedTerm := do
    keyword "refl"
    symbol "("
    let value ← term
    symbol ")"
    pure (.refl value)
  grouped : Parser NamedTerm := do
    symbol "("
    let first ← term
    let result ← (symbol "," *> (NamedTerm.pair first <$> term)) <|>
      (symbol ":" *> (NamedTerm.ann first <$> term)) <|> pure first
    symbol ")"
    pure result
  atom : Parser NamedTerm :=
    (symbol "π₁" *> (NamedTerm.first <$> atom)) <|>
      (symbol "π₂" *> (NamedTerm.second <$> atom)) <|>
      (symbol "𝕌" *> pure .univ) <|>
      (symbol "𝟙" *> pure .unitType) <|>
      (keyword "tt" *> pure .unitVal) <|>
      triple "Id" NamedTerm.idType <|>
      reflTerm <|>
      triple "J" NamedTerm.elimId <|>
      (NamedTerm.var <$> identifier) <|>
      grouped
  application : Parser NamedTerm := do
    let first ← atom
    let rest ← many atom
    let left := rest.foldl NamedTerm.app first
    (symbol "→" *> (fun right => NamedTerm.pi left (BoundSyntax.ofBinder Raw.wildcard right)) <$> term) <|>
      (symbol "×" *> (fun right => NamedTerm.sigma left (BoundSyntax.ofBinder Raw.wildcard right)) <$> term) <|>
      pure left

private def command : Parser Command :=
  define <|> checkTerm <|> (keyword "compute" *> ((Command.compute ∘ NamedTerm.toRaw) <$> term))
where
  define : Parser Command := do
    keyword "def"
    let name ← identifier
    let parameters ← optional do
      keyword "over"
      symbol "("
      let names ← optional do
        let first ← identifier
        let rest ← many (symbol "," *> identifier)
        pure (first :: rest.toList)
      symbol ")"
      pure (names.getD [])
    symbol ":"
    let type ← term
    symbol ":="
    let value ← term
    pure (match parameters with
      | none => .define name type.toRaw value.toRaw
      | some names => .defineOver name names type.toRaw value.toRaw)
  checkTerm : Parser Command := do
    keyword "check"
    let value ← term
    symbol ":"
    let type ← term
    pure (.check value.toRaw type.toRaw)

def parseTerm (source : String) : Except String Raw :=
  (trivia *> (NamedTerm.toRaw <$> term) <* eof).run source

def parseProgram (source : String) : Except String Program := parser.run source
where
  parser : Parser Program := do
    trivia
    let moduleName ← optional (keyword "module" *> identifier <* optional (symbol ";"))
    let commands ← many (command <* optional (symbol ";"))
    eof
    pure ⟨moduleName, commands⟩

private structure ParameterHeader where
  name : String
  includes : Array String
  parameters : Array Parameter

private inductive SourceUnit where
  | module (header : ParameterHeader) (imports : Array String) (commands : Array Command)
  | telescope (header : ParameterHeader)

private def parameterHeader : Parser ParameterHeader := do
  let name ← identifier
  let includes ← many (keyword "include" *> identifier)
  let parameters ← many do
    symbol "("
    let name ← identifier
    symbol ":"
    let type ← term
    symbol ")"
    pure (⟨name, type.toRaw⟩ : Parameter)
  let _ ← optional (symbol ";")
  pure ⟨name, includes, parameters⟩

private def sourceUnit : Parser SourceUnit :=
  (keyword "telescope" *> (SourceUnit.telescope <$> parameterHeader)) <|> do
    keyword "module"
    let header ← parameterHeader
    let imports ← many (keyword "import" *> identifier <* optional (symbol ";"))
    let commands ← many (command <* optional (symbol ";"))
    pure (.module header imports commands)

private def distinctParameters (owner : String) (parameters : Array Parameter) : Except String Unit := do
  let mut seen : List String := []
  for param in parameters do
    if seen.contains param.name then
      throw s!"duplicate parameter '{param.name}' in {owner}"
    seen := param.name :: seen

/-- Memoize expanded raw headers. Their field types are checked in each including module. -/
private partial def expandTelescope (declared : List (String × ParameterHeader))
    (path : List String) (expanded : List (String × Array Parameter)) (name : String) :
    Except String (List (String × Array Parameter) × Array Parameter) := do
  if path.contains name then
    throw s!"cyclic telescope includes: {String.intercalate " -> " (name :: path).reverse}"
  if let some params := expanded.lookup name then
    return (expanded, params)
  let some header := declared.lookup name
    | throw s!"missing telescope '{name}' in include chain {String.intercalate " -> " path.reverse}"
  let mut expanded := expanded
  let mut params := #[]
  for included in header.includes do
    let (next, fields) ← expandTelescope declared (name :: path) expanded included
    expanded := next
    params := params ++ fields
  params := params ++ header.parameters
  distinctParameters s!"telescope '{name}'" params
  pure ((name, params) :: expanded, params)

private def expandSource (units : Array SourceUnit) : Except String (Array Module) := do
  let mut declared : List (String × ParameterHeader) := []
  for unit in units do
    if let .telescope header := unit then
      if (declared.lookup header.name).isSome then
        throw s!"duplicate telescope '{header.name}'"
      declared := (header.name, header) :: declared
  let mut expanded : List (String × Array Parameter) := []
  for (name, _) in declared.reverse do
    let (next, _) ← expandTelescope declared [] expanded name
    expanded := next
  let mut modules := #[]
  for unit in units do
    if let .module header imports commands := unit then
      let mut params := #[]
      for name in header.includes do
        let some fields := expanded.lookup name
          | throw s!"missing telescope '{name}' in module '{header.name}'"
        params := params ++ fields
      params := params ++ header.parameters
      unless header.includes.isEmpty do
        distinctParameters s!"module '{header.name}'" params
      modules := modules.push ⟨header.name, params, imports, commands⟩
  pure modules

def parseModules (source : String) : Except String (Array Module) := do
  expandSource (← (trivia *> many1 sourceUnit <* eof).run source)

/-- Parse a standalone program or expand the headers of a module source. -/
def parseInput (source : String) : Except String Input := do
  let input ← parser.run source
  match input with
  | .inr program => pure (.standalone program)
  | .inl units =>
    if let #[.module header imports commands] := units then
      if header.includes.isEmpty && header.parameters.isEmpty && imports.isEmpty then
        return .standalone ⟨some header.name, commands⟩
    pure (.modules (← expandSource units))
where
  parser : Parser (Sum (Array SourceUnit) Program) := do
    trivia
    let input ← (Sum.inl <$> many1 sourceUnit) <|> do
      let commands ← many (command <* optional (symbol ";"))
      pure (.inr ⟨none, commands⟩)
    eof
    pure input

end Parser

inductive CommandResult where
  | defined (name : String)
  | checked (term type : String)
  | computed (value : String)
  deriving Repr, DecidableEq

instance : ToString CommandResult where
  toString
    | .defined name => s!"✓ defined {name}"
    | .checked term type => s!"✓ {term} : {type}"
    | .computed value => s!"↦ {value}"

def checkQuery (ctx : Context scope) (fuel : Nat) (term type : Term scope)
    (display : Term scope → String) : Except String CommandResult := do
  (checkDefinition ctx fuel type term).mapError toString
  pure (.checked (display term) (display type))

def computeQuery (ctx : Context scope) (fuel : Nat) (term : Term scope)
    (display : Term scope → String) : Except String CommandResult := do
  let _ ← (infer ctx fuel term).mapError toString
  let normal ← (nf scope ctx.definitions fuel term).mapError fun
    | .outOfFuel => "evaluation ran out of fuel"
  pure (.computed (display normal))

def resolveTerm (scope : Scope) (resolve : String → Option (Name scope)) (raw : Raw)
    (missing : String → String := fun name => s!"unbound name '{name}'") :
    Except String (Term scope) :=
  (AST.fromNamed scope resolve raw).mapError fun
    | .unbound name => missing name
    | .duplicateBinder names => s!"duplicate name in binder pattern ({String.intercalate ", " names})"

private structure Environment where
  scope : Scope
  context : Context scope
  names : List (String × Name scope)

private def Environment.empty : Environment := ⟨[], .empty, []⟩

private def Environment.extend (env : Environment) (name : String)
    (type value : Term env.scope) : Environment :=
  let id := env.scope.nextId
  let outer : env.scope ⊆ id :: env.scope := fun {_} mem => List.mem_cons_of_mem _ mem
  { scope := id :: env.scope
    context := env.context.extend id (env.scope.nextId_not_mem) type (some value)
    names := (name, env.scope.fresh) :: env.names.map (fun (text, key) => (text, key.sink outer)) }

private def Environment.resolve (env : Environment) (term : Raw) : Except String (Term env.scope) :=
  resolveTerm env.scope (fun name => env.names.lookup name) term

private def Environment.display (env : Environment) (term : Term env.scope) : String :=
  prettyTerm env.scope term fun key =>
    (env.names.findSome? (fun (name, candidate) =>
      if candidate.id == key.id then some name else none)).getD s!"x{key.id}"

private def runCommand (env : Environment) (fuel : Nat) (command : Command) :
    Except String (Environment × CommandResult) := do
  match command with
  | .define name rawType rawValue | .defineOver name [] rawType rawValue =>
    if (env.names.lookup name).isSome then
      throw s!"duplicate definition '{name}'"
    let type ← env.resolve rawType
    let value ← env.resolve rawValue
    (checkDefinition env.context fuel type value).mapError toString
    pure (env.extend name type value, .defined name)
  | .defineOver _ _ _ _ => throw "an 'over' clause in a standalone program must be empty"
  | .check rawTerm rawType => do
    let term ← env.resolve rawTerm
    let type ← env.resolve rawType
    pure (env, ← checkQuery env.context fuel term type env.display)
  | .compute rawTerm => do
    let term ← env.resolve rawTerm
    pure (env, ← computeQuery env.context fuel term env.display)

/-- Run commands in order, keeping the environment from the last successful command. -/
def runProgram (program : Program) (fuel : Nat := 1024) : Array (Except String CommandResult) := Id.run do
  let mut env := Environment.empty
  let mut results := #[]
  for command in program.commands do
    match runCommand env fuel command with
    | .ok (next, result) =>
      env := next
      results := results.push (.ok result)
    | .error error => results := results.push (.error error)
  return results

end FreeFoil.Examples.MLTT

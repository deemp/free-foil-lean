import FreeFoil.Named
import Lean

namespace FreeFoil

/-- A recursive field whose body has the pattern's names in scope. -/
structure BoundSyntax (Pattern : Type) (arity : Pattern → Nat) (Body : Type) where
  shape : Pattern
  names : List String
  length_eq : names.length = arity shape
  body : Body

def BoundSyntax.ofBinder (binder : Binder sig String) (body : Body) :
    BoundSyntax sig.Pattern sig.binders Body :=
  ⟨binder.shape, binder.names, binder.arity, body⟩

namespace Derive

open Lean Elab Command Meta Parser.Term

private inductive FieldKind where
  | term (category : Lean.Name)
  | scoped (category : Lean.Name)
  | payload (type : Expr)

private structure Field where
  name : Lean.Name
  kind : FieldKind

private structure Operator where
  ctor : Lean.Name
  label : Lean.Name
  fields : Array Field

private structure Category where
  source : Lean.Name
  hasVar : Bool
  recursive : Bool
  operators : Array Operator

private def shortName (name : Lean.Name) : Lean.Name := Lean.Name.mkSimple name.getString!

private def Operator.tag (op : Operator) : Lean.Name := `Op ++ op.label

private def Field.isScoped (field : Field) : Bool :=
  match field.kind with | .scoped _ => true | _ => false

private def Operator.rawHelper (op : Operator) : Lean.Name :=
  `Raw ++ if op.fields.any Field.isScoped then op.label.appendAfter "Scoped" else op.label

private def fieldKind (sources : Array Lean.Name) (pattern arity : Lean.Name)
    (ctor : Lean.Name) (type : Expr) : MetaM FieldKind := do
  for source in sources do
    if type.isConstOf source then return .term source
    let bound := mkApp3 (mkConst ``BoundSyntax) (mkConst pattern) (mkConst arity) (mkConst source)
    if type == bound then return .scoped source
  if type.hasFVar || (type.find? fun expr => sources.any expr.isConstOf).isSome then
    throwError "unsupported dependent or nested field type {type} in {ctor}"
  return .payload type

private def readCategory (sources : Array Lean.Name) (family : Bool)
    (pattern arity source : Lean.Name) : MetaM Category := do
  let info ← getConstInfoInduct source
  unless info.numParams == 0 && info.numIndices == 0 do
    throwError "expected an unparameterized syntax inductive, got {source}"
  unless info.all.all (sources.contains ·) do
    throwError "include all mutually recursive syntax inductives that contain {source}"
  let varCtor := source ++ `var
  let hasVar := info.ctors.contains varCtor
  unless hasVar || family do
    throwError "expected a constructor {varCtor} : String → {source}"
  let mut operators := #[]
  for ctor in info.ctors do
    let ctorInfo ← getConstInfoCtor ctor
    let fields ← forallTelescope ctorInfo.type fun xs _ => do
      let fields ← xs.mapM fun x => do
        let field ← x.fvarId!.getDecl
        unless field.binderInfo.isExplicit do
          throwError "expected an explicit field of {ctor}"
        return field
      if ctor == varCtor then
        unless fields.map (·.type) == #[mkConst ``String] do
          throwError "expected {varCtor} : String → {source}"
        return #[]
      fields.mapM fun field => do
        return ⟨field.userName, ← fieldKind sources pattern arity ctor field.type⟩
    unless ctor == varCtor do
      let label := if family then shortName source ++ shortName ctor else shortName ctor
      operators := operators.push ⟨ctor, label, fields⟩
  return ⟨source, hasVar, info.isRec, operators⟩

private def emitSignature (pattern arity : Ident) (operators : Array Operator) :
    CommandElabM Unit := do
  let ctors ← operators.mapM fun op => do
    let mut params := #[]
    for field in op.fields do
      if let .payload type := field.kind then
        let type ← liftTermElabM (PrettyPrinter.delab type)
        params := params.push (← `(bracketedBinder| ($(mkIdent field.name) : $type)))
    let label := mkIdent op.label
    let decl ← `(Lean.Parser.Command.optDeclSig| $params*)
    `(Lean.Parser.Command.ctor| | $label:ident $decl)
  let op := mkIdent `Op
  elabCommand (← `(inductive $op:ident where $ctors* deriving DecidableEq))
  let arities (countScopes : Bool) : CommandElabM (Array (TSyntax ``matchAlt)) :=
    operators.mapM fun op => do
      let mut count := 0
      let mut payloads := #[]
      for field in op.fields do
        match field.kind with
        | .payload _ => payloads := payloads.push (← `(_))
        | .term _ => if !countScopes then count := count + 1
        | .scoped _ => if countScopes then count := count + 1
      let arity := Lean.Syntax.mkNumLit (toString count)
      `(matchAltExpr| | $(mkIdent op.tag):ident $payloads* => $arity)
  let sig := mkIdent `sig
  let raw := mkIdent `Raw
  let term := mkIdent `Term
  if operators.isEmpty then
    elabCommand (← `(abbrev $sig:ident : Signature where
      Op := $op
      Pattern := $pattern
      terms x := nomatch x
      scopes x := nomatch x
      binders := $arity))
  else
    let terms ← arities false
    let scopes ← arities true
    elabCommand (← `(abbrev $sig:ident : Signature where
      Op := $op
      Pattern := $pattern
      terms := fun $terms:matchAlt*
      scopes := fun $scopes:matchAlt*
      binders := $arity))
  elabCommand (← `(abbrev $raw:ident := Syntax $sig String))
  elabCommand (← `(abbrev $term:ident := AST $sig))

private def finFunction (items : Array Term) : CommandElabM Term := do
  items.foldrM (fun item rest => `(Fin.cases $item $rest)) (← `(Fin.elim0))

private def fieldName (kind : Lean.Name) (i : Nat) : Ident :=
  mkIdent (kind.appendIndexAfter i)

private def emitHelpers (operators : Array Operator) (hasVar : Bool) : CommandElabM Unit := do
  let sig := mkIdent `sig
  let raw := mkIdent `Raw
  let term := mkIdent `Term
  if hasVar then
    let rawVar := mkIdent `Raw.var
    let termVar := mkIdent `Term.var
    elabCommand (← `(def $rawVar:ident (name : String) : $raw := Syntax.var name))
    elabCommand (← `(def $termVar:ident {scope : Scope} (name : Name scope) : $term scope :=
      AST.var name))
  for op in operators do
    let mut rawParams := #[]
    let mut termParams := #[]
    let mut terms := #[]
    let mut binders := #[]
    let mut bodies := #[]
    let mut payloads := #[]
    for field in op.fields do
      let arg := mkIdent field.name
      match field.kind with
      | .term _ =>
        rawParams := rawParams.push (← `(bracketedBinder| ($arg : $raw)))
        termParams := termParams.push (← `(bracketedBinder| ($arg : $term scope)))
        terms := terms.push (← `($arg:ident))
      | .scoped _ =>
        let binder := mkIdent (← liftCoreM (mkFreshUserName (field.name.appendAfter "Binder")))
        rawParams := rawParams.push (← `(bracketedBinder| ($binder : Binder $sig String)))
        rawParams := rawParams.push (← `(bracketedBinder| ($arg : $raw)))
        termParams := termParams.push (← `(bracketedBinder| ($arg : ScopedAST $sig scope)))
        binders := binders.push (← `($binder:ident))
        bodies := bodies.push (← `($arg:ident))
      | .payload type =>
        let type ← liftTermElabM (PrettyPrinter.delab type)
        let param ← `(bracketedBinder| ($arg : $type))
        rawParams := rawParams.push param
        termParams := termParams.push param
        payloads := payloads.push (← `($arg:ident))
    let tag ← `($(mkIdent op.tag):ident $payloads*)
    let ordinary ← finFunction terms
    let patterns ← finFunction binders
    let scopedBodies ← finFunction bodies
    let rawHelper := mkIdent op.rawHelper
    let termHelper := mkIdent (`Term ++ op.label)
    elabCommand (← `(def $rawHelper:ident $rawParams* : $raw :=
      Syntax.node ($tag) $ordinary $patterns $scopedBodies))
    elabCommand (← `(def $termHelper:ident {scope : Scope} $termParams* : $term scope :=
      AST.node ($tag) $ordinary $scopedBodies))

private def codecName (source direction : Lean.Name) : Ident :=
  mkIdent (shortName source ++ direction)

private def emitCodec (category : Category) (operators : Array Operator) (family : Bool) :
    CommandElabM (TSyntax `command × TSyntax `command) := do
  let raw := mkIdent `Raw
  let decl := mkIdent category.source
  let toRaw := codecName category.source `toRaw
  let fromRaw := codecName category.source `fromRaw
  let mut toAlts := #[]
  let mut fromAlts := #[]
  if category.hasVar then
    let varCtor := mkIdent (category.source ++ `var)
    toAlts := toAlts.push (← `(matchAltExpr| | $varCtor:ident name => Syntax.var name))
    let varBody ← if family then `(some ($varCtor name)) else `($varCtor name)
    fromAlts := fromAlts.push (← `(matchAltExpr| | Syntax.var name => $varBody))
  for op in category.operators do
    let ctor := mkIdent op.ctor
    let terms := mkIdent `terms
    let binders := mkIdent `binders
    let bodies := mkIdent `bodies
    let mut fields := #[]
    let mut toArgs := #[]
    let mut fromArgs := #[]
    let mut payloads := #[]
    let mut decoders := #[]
    let mut termIndex := 0
    let mut scopeIndex := 0
    for (field, i) in op.fields.zipIdx do
      let arg := fieldName `arg i
      match field.kind with
      | .term child =>
        let encode := codecName child `toRaw
        let decode := codecName child `fromRaw
        fields := fields.push (← `($arg:ident))
        toArgs := toArgs.push (← `($encode $arg))
        let idx := Lean.Syntax.mkNumLit (toString termIndex)
        let decoded ← `($decode ($terms $idx))
        if family then
          decoders := decoders.push (arg, decoded)
          fromArgs := fromArgs.push (← `($arg:ident))
        else
          fromArgs := fromArgs.push decoded
        termIndex := termIndex + 1
      | .scoped child =>
        let encode := codecName child `toRaw
        let decode := codecName child `fromRaw
        let shape := fieldName `shape i
        let names := fieldName `names i
        let length := fieldName `length i
        fields := fields.push (← `(BoundSyntax.mk $shape $names $length $arg))
        toArgs := toArgs.push (← `(⟨$shape, $names, $length⟩))
        toArgs := toArgs.push (← `($encode $arg))
        let idx := Lean.Syntax.mkNumLit (toString scopeIndex)
        let decoded ← `($decode ($bodies $idx))
        if family then
          decoders := decoders.push (arg, decoded)
          fromArgs := fromArgs.push (← `(BoundSyntax.ofBinder ($binders $idx) $arg))
        else
          fromArgs := fromArgs.push (← `(BoundSyntax.ofBinder ($binders $idx) $decoded))
        scopeIndex := scopeIndex + 1
      | .payload _ =>
        let arg ← `($arg:ident)
        fields := fields.push arg
        toArgs := toArgs.push arg
        fromArgs := fromArgs.push arg
        payloads := payloads.push arg
    let helper := mkIdent op.rawHelper
    toAlts := toAlts.push (← `(matchAltExpr| | $ctor:ident $fields* => $helper $toArgs*))
    let tag ← `($(mkIdent op.tag):ident $payloads*)
    let mut decoded ← `($ctor $fromArgs*)
    if family then
      decoded ← `(some ($decoded))
      decoded ← decoders.foldrM (fun (arg, branch) rest => `(Option.bind $branch (fun $arg => $rest))) decoded
    fromAlts := fromAlts.push (← `(matchAltExpr|
      | Syntax.node ($tag) $terms $binders $bodies => $decoded))
  if family then
    fromAlts := fromAlts.push (← `(matchAltExpr| | _ => none))
  else if operators.isEmpty then
    fromAlts := fromAlts.push (← `(matchAltExpr| | Syntax.node op _ _ _ => nomatch op))
  let value := mkIdent `value
  let toBody ← if toAlts.isEmpty then `(nomatch $value) else
    `(match $value:ident with $toAlts:matchAlt*)
  let fromBody ← `(match $value:ident with $fromAlts:matchAlt*)
  let result ← if family then `(Option $decl) else `($decl:ident)
  if category.recursive then
    return (← `(def $toRaw:ident ($value : $decl) : $raw := $toBody
      termination_by structural $value:ident),
      ← `(def $fromRaw:ident ($value : $raw) : $result := $fromBody
        termination_by structural $value:ident))
  return (← `(def $toRaw:ident ($value : $decl) : $raw := $toBody),
    ← `(def $fromRaw:ident ($value : $raw) : $result := $fromBody))

private def emitResolution (source : Lean.Name) (family : Bool) : CommandElabM Unit := do
  let term := mkIdent `Term
  let decl := mkIdent source
  let sig := mkIdent `sig
  let toRaw := codecName source `toRaw
  let fromRaw := codecName source `fromRaw
  let resolve := codecName source `resolve
  let resolveClosed := codecName source `resolveClosed
  let toDeclaration := mkIdent (Lean.Name.str `Term ("to" ++ source.getString!))
  let result ← if family then `(Option $decl) else `($decl:ident)
  elabCommand (← `(def $resolve:ident (scope : Scope)
      (lookup : String → Option (Name scope)) (value : $decl) :
      Except (ResolveError String) ($term scope) :=
    AST.fromNamed (sig := $sig) scope lookup ($toRaw value)))
  elabCommand (← `(def $resolveClosed:ident (value : $decl) :
      Except (ResolveError String) ($term []) :=
    AST.fromClosed ($toRaw value)))
  elabCommand (← `(def $toDeclaration:ident (scope : Scope) (value : $term scope)
      (freeName : Name scope → String) : $result :=
    $fromRaw (AST.toNamed scope value freeName)))

private def deriveFamily (sourceIds : Array Ident) (pattern arity : Ident) (family : Bool) :
    CommandElabM Unit := do
  let sources ← liftTermElabM (sourceIds.mapM fun id => do
    realizeGlobalConstNoOverloadWithInfo id)
  let labels := sources.toList.map shortName
  unless labels.Nodup do
    throwError "each Free Foil syntax category must have a distinct name"
  let patternName ← liftTermElabM (realizeGlobalConstNoOverloadWithInfo pattern)
  let arityName ← liftTermElabM (realizeGlobalConstNoOverloadWithInfo arity)
  let categories ← liftTermElabM (sources.mapM fun source =>
    readCategory sources family patternName arityName source)
  let operators := categories.flatMap (·.operators)
  emitSignature (mkIdent patternName) (mkIdent arityName) operators
  emitHelpers operators (categories.any (·.hasVar))
  let codecs ← categories.mapM fun category => emitCodec category operators family
  if family then
    let encoders := codecs.map Prod.fst
    let decoders := codecs.map Prod.snd
    elabCommand (← `(mutual $encoders* end))
    elabCommand (← `(mutual $decoders* end))
  else
    for (encode, decode) in codecs do
      elabCommand encode
      elabCommand decode
  for source in sources do
    emitResolution source family

/-- Derive `Op`, `sig`, `Raw`, `Term`, and their constructors and conversions.
The source inductive has a `var : String → Source` constructor. Other constructors take
ordinary recursive fields, `BoundSyntax Pattern arity Source` fields, or fixed payloads. -/
elab "derive_free_foil " source:ident " with " pattern:ident ", " arity:ident : command =>
  deriveFamily #[source] pattern arity false

/-- Derive a shared Free Foil signature for several syntax categories. Each category
has its own constructor namespace and codecs. Decoding from the common representation
checks that a tree uses the requested category and the declared categories of its children. -/
elab "derive_free_foil " "[" sources:ident,+ "]" " with " pattern:ident ", " arity:ident : command =>
  deriveFamily sources.getElems pattern arity true

end Derive
end FreeFoil

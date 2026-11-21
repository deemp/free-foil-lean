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
  | term
  | scoped
  deriving DecidableEq

private structure Field where
  name : Lean.Name
  kind : FieldKind

private structure Operator where
  ctor : Lean.Name
  fields : Array Field

private def Operator.label (op : Operator) : Lean.Name := op.ctor.getString! |> Lean.Name.mkSimple

private def Operator.tag (op : Operator) : Lean.Name := `Op ++ op.label

private def Operator.rawHelper (op : Operator) : Lean.Name :=
  let suffix := if op.fields.any (·.kind == .scoped) then "Scoped" else ""
  `Raw ++ op.label.appendAfter suffix

private def readOperators (raw pattern arity : Lean.Name) : MetaM (Array Operator) := do
  let info ← getConstInfoInduct raw
  unless info.numParams == 0 && info.numIndices == 0 && info.all == [raw] do
    throwError "expected a single unparameterized syntax inductive"
  let varCtor := raw ++ `var
  unless info.ctors.contains varCtor do
    throwError "expected a constructor {varCtor} : String → {raw}"
  let mut operators := #[]
  for ctor in info.ctors do
    let info ← getConstInfoCtor ctor
    let fields ← forallTelescope info.type fun xs _ => do
      let fields ← xs.mapM fun x => do
        let field ← x.fvarId!.getDecl
        unless field.binderInfo.isExplicit do
          throwError "expected an explicit field of {ctor}"
        return field
      if ctor == varCtor then
        unless fields.map (·.type) == #[mkConst ``String] do
          throwError "expected {varCtor} : String → {raw}"
        return #[]
      let bound := mkApp3 (mkConst ``BoundSyntax) (mkConst pattern) (mkConst arity) (mkConst raw)
      fields.mapM fun field => do
        if field.type == mkConst raw then
          return ⟨field.userName, .term⟩
        if field.type == bound then
          return ⟨field.userName, .scoped⟩
        throwError "unsupported field type {field.type} in {ctor}"
    unless ctor == varCtor do
      operators := operators.push ⟨ctor, fields⟩
  return operators

private def emitSignature (pattern arity : Ident) (operators : Array Operator) :
    CommandElabM Unit := do
  let ctors ← operators.mapM fun op =>
    `(Lean.Parser.Command.ctor| | $(mkIdent op.label):ident)
  let op := mkIdent `Op
  elabCommand (← `(inductive $op:ident where $ctors* deriving DecidableEq))
  let arities (kind : FieldKind) : CommandElabM (Array (TSyntax ``matchAlt)) :=
    operators.mapM fun op => do
      let count := Lean.Syntax.mkNumLit (toString (op.fields.filter (·.kind == kind)).size)
      `(matchAltExpr| | $(mkIdent op.tag):ident => $count)
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
    let terms ← arities .term
    let scopes ← arities .scoped
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

private def emitHelpers (operators : Array Operator) : CommandElabM Unit := do
  let sig := mkIdent `sig
  let raw := mkIdent `Raw
  let term := mkIdent `Term
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
    for field in op.fields do
      let arg := mkIdent field.name
      match field.kind with
      | .term =>
        rawParams := rawParams.push (← `(bracketedBinder| ($arg : $raw)))
        termParams := termParams.push (← `(bracketedBinder| ($arg : $term scope)))
        terms := terms.push (← `($arg:ident))
      | .scoped =>
        let binder := mkIdent (← liftCoreM (mkFreshUserName (field.name.appendAfter "Binder")))
        rawParams := rawParams.push (← `(bracketedBinder| ($binder : Binder $sig String)))
        rawParams := rawParams.push (← `(bracketedBinder| ($arg : $raw)))
        termParams := termParams.push (← `(bracketedBinder| ($arg : ScopedAST $sig scope)))
        binders := binders.push (← `($binder:ident))
        bodies := bodies.push (← `($arg:ident))
    let tag := mkIdent op.tag
    let ordinary ← finFunction terms
    let patterns ← finFunction binders
    let scopedBodies ← finFunction bodies
    let rawHelper := mkIdent op.rawHelper
    let termHelper := mkIdent (`Term ++ op.label)
    elabCommand (← `(def $rawHelper:ident $rawParams* : $raw :=
      Syntax.node $tag $ordinary $patterns $scopedBodies))
    elabCommand (← `(def $termHelper:ident {scope : Scope} $termParams* : $term scope :=
      AST.node $tag $ordinary $scopedBodies))

private def emitConversions (source : Lean.Name) (operators : Array Operator) :
    CommandElabM Unit := do
  let sig := mkIdent `sig
  let raw := mkIdent `Raw
  let term := mkIdent `Term
  let decl := mkIdent source
  let sourceLabel := Lean.Name.mkSimple source.getString!
  let toRaw := mkIdent (sourceLabel ++ `toRaw)
  let fromRaw := mkIdent (sourceLabel ++ `fromRaw)
  let varCtor := mkIdent (source ++ `var)
  let mut toAlts := #[← `(matchAltExpr| | $varCtor:ident name => Syntax.var name)]
  let mut fromAlts := #[← `(matchAltExpr| | Syntax.var name => $varCtor name)]
  for op in operators do
    let ctor := mkIdent op.ctor
    let terms := mkIdent `terms
    let binders := mkIdent `binders
    let bodies := mkIdent `bodies
    let mut fields := #[]
    let mut toArgs := #[]
    let mut fromArgs := #[]
    let mut termIndex := 0
    let mut scopeIndex := 0
    for (field, i) in op.fields.zipIdx do
      let arg := fieldName `arg i
      match field.kind with
      | .term =>
        fields := fields.push (← `($arg:ident))
        toArgs := toArgs.push (← `($toRaw $arg))
        let idx := Lean.Syntax.mkNumLit (toString termIndex)
        fromArgs := fromArgs.push (← `($fromRaw ($terms $idx)))
        termIndex := termIndex + 1
      | .scoped =>
        let shape := fieldName `shape i
        let names := fieldName `names i
        let length := fieldName `length i
        fields := fields.push (← `(BoundSyntax.mk $shape $names $length $arg))
        toArgs := toArgs.push (← `(⟨$shape, $names, $length⟩))
        toArgs := toArgs.push (← `($toRaw $arg))
        let idx := Lean.Syntax.mkNumLit (toString scopeIndex)
        fromArgs := fromArgs.push
          (← `(BoundSyntax.ofBinder ($binders $idx) ($fromRaw ($bodies $idx))))
        scopeIndex := scopeIndex + 1
    let helper := mkIdent op.rawHelper
    toAlts := toAlts.push (← `(matchAltExpr| | $ctor:ident $fields* => $helper $toArgs*))
    let tag := mkIdent op.tag
    fromAlts := fromAlts.push (← `(matchAltExpr|
      | Syntax.node $tag $terms $binders $bodies => $ctor $fromArgs*))
  if operators.isEmpty then
    fromAlts := fromAlts.push (← `(matchAltExpr| | Syntax.node op _ _ _ => nomatch op))
  let value := mkIdent `value
  let toBody ← `(match $value:ident with $toAlts:matchAlt*)
  let fromBody ← `(match $value:ident with $fromAlts:matchAlt*)
  if operators.any (!·.fields.isEmpty) then
    elabCommand (← `(def $toRaw:ident ($value : $decl) : $raw := $toBody
      termination_by structural $value:ident))
    elabCommand (← `(def $fromRaw:ident ($value : $raw) : $decl := $fromBody
      termination_by structural $value:ident))
  else
    elabCommand (← `(def $toRaw:ident ($value : $decl) : $raw := $toBody))
    elabCommand (← `(def $fromRaw:ident ($value : $raw) : $decl := $fromBody))
  let resolve := mkIdent (sourceLabel ++ `resolve)
  let resolveClosed := mkIdent (sourceLabel ++ `resolveClosed)
  let toDeclaration := mkIdent (Lean.Name.str `Term ("to" ++ source.getString!))
  elabCommand (← `(def $resolve:ident (scope : Scope)
      (lookup : String → Option (Name scope)) (value : $decl) :
      Except (ResolveError String) ($term scope) :=
    AST.fromNamed (sig := $sig) scope lookup ($toRaw value)))
  elabCommand (← `(def $resolveClosed:ident (value : $decl) :
      Except (ResolveError String) ($term []) :=
    AST.fromClosed ($toRaw value)))
  elabCommand (← `(def $toDeclaration:ident (scope : Scope) (value : $term scope)
      (freeName : Name scope → String) : $decl :=
    $fromRaw (AST.toNamed scope value freeName)))

/-- Derive `Op`, `sig`, `Raw`, `Term`, and their constructors and conversions.
The source inductive has a `var : String → Source` constructor. Other constructors take
ordinary recursive fields or `BoundSyntax Pattern arity Source` fields. -/
elab "derive_free_foil " source:ident " with " pattern:ident ", " arity:ident : command => do
  let sourceName ← liftTermElabM (realizeGlobalConstNoOverloadWithInfo source)
  let patternName ← liftTermElabM (realizeGlobalConstNoOverloadWithInfo pattern)
  let arityName ← liftTermElabM (realizeGlobalConstNoOverloadWithInfo arity)
  let operators ← liftTermElabM (readOperators sourceName patternName arityName)
  emitSignature (mkIdent patternName) (mkIdent arityName) operators
  emitHelpers operators
  emitConversions sourceName operators

end Derive
end FreeFoil

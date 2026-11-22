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

/-- Lists and options surrounding a recursive field. Used in generated constructor
arities and conversions. -/
inductive FieldLayout where
  | child
  | list (element : FieldLayout)
  | optional (element : FieldLayout)
  deriving BEq

abbrev FieldLayout.Values : FieldLayout → Type → Type
  | .child, α => α
  | .list element, α => List (element.Values α)
  | .optional element, α => Option (element.Values α)

def FieldLayout.shape {α : Type} :
    (layout : FieldLayout) → layout.Values α → layout.Values Unit
  | .child, _ => ()
  | .list element, values => values.map (element.shape (α := α))
  | .optional element, value => value.map (element.shape (α := α))

def FieldLayout.count : (layout : FieldLayout) → layout.Values Unit → Nat
  | .child, _ => 1
  | .list element, values => values.foldr (fun value n => element.count value + n) 0
  | .optional _, none => 0
  | .optional element, some value => element.count value

def FieldLayout.index {α : Type} :
    (layout : FieldLayout) → (values : layout.Values α) →
      Fin (layout.count (layout.shape values)) → α
  | .child, value => fun _ => value
  | .list element, values => listIndex element values
  | .optional _, none => Fin.elim0
  | .optional element, some value => element.index value
where
  listIndex (element : FieldLayout) : (values : List (element.Values α)) →
      Fin ((FieldLayout.list element).count ((FieldLayout.list element).shape values)) → α
    | [] => Fin.elim0
    | value :: values => Fin.addCases (element.index value) (listIndex element values)

def FieldLayout.traverse {m : Type → Type} [Applicative m] {α : Type} :
    (layout : FieldLayout) → (shape : layout.Values Unit) →
      (Fin (layout.count shape) → m α) → m (layout.Values α)
  | .child, (), read => read ⟨0, by simp [FieldLayout.count]⟩
  | .list element, shapes, read => listTraverse element shapes read
  | .optional _, none, _ => pure none
  | .optional element, some shape, read => some <$> element.traverse shape read
where
  listTraverse (element : FieldLayout) : (shapes : List (element.Values Unit)) →
      (Fin ((FieldLayout.list element).count shapes) → m α) → m (List (element.Values α))
    | [], _ => pure []
    | shape :: shapes, read =>
      List.cons <$> element.traverse shape (fun i => read (i.castAdd _))
        <*> listTraverse element shapes (fun i => read (i.natAdd (element.count shape)))

private inductive FieldKind where
  | recursive (category : Lean.Name) (scopedField : Bool) (layout : FieldLayout)
  | payload (type : Term)

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
  operators : Array Operator

private def shortName (name : Lean.Name) : Lean.Name := Lean.Name.mkSimple name.getString!

private def Operator.tag (op : Operator) : Lean.Name := `Op ++ op.label

private def Field.isScoped (field : Field) : Bool :=
  match field.kind with | .recursive _ scopedField _ => scopedField | _ => false

private def Operator.rawHelper (op : Operator) : Lean.Name :=
  `Raw ++ if op.fields.any Field.isScoped then op.label.appendAfter "Scoped" else op.label

private def hasSource (sources : Array Lean.Name) (type : Expr) : Bool :=
  (type.find? fun expr => sources.any expr.isConstOf).isSome

private def recursiveField (sources : Array Lean.Name) (parameters : Array Expr)
    (pattern arity ctor : Lean.Name) (type : Expr) : MetaM FieldKind := do
  if let .app (.const container _) item := type then
    if container == ``List || container == ``Option then
      let .recursive child scopedField element ← recursiveField sources parameters pattern arity ctor item
        | throwError "unsupported recursive field type {type} in {ctor}"
      return .recursive child scopedField (if container == ``List then .list element else .optional element)
  let scopedField := type.isAppOfArity ``BoundSyntax 3
  let body := if scopedField then type.appArg! else type
  if scopedField then
    let args := type.getAppArgs
    unless args[0]!.isConstOf pattern && args[1]!.isConstOf arity do
      throwError "expected the declared pattern and arity in scoped field {type} of {ctor}"
  let some child := body.getAppFn.constName? | throwError "unsupported recursive field type {type} in {ctor}"
  unless sources.contains child do
    throwError "unsupported recursive field type {type} in {ctor}; use List, Option, or BoundSyntax"
  unless body.getAppArgs == parameters do
    throwError "recursive field {type} in {ctor} must use the syntax parameters in order"
  return .recursive child scopedField .child

private def readCategory (sources : Array Lean.Name) (family : Bool) (parameters : Array Expr)
    (pattern arity source : Lean.Name) : MetaM Category := do
  let info ← getConstInfoInduct source
  unless info.numIndices == 0 do
    throwError "indexed syntax inductive {source} is unsupported"
  unless info.numParams == parameters.size do
    throwError "all syntax categories must have the same number of type parameters; got {source}"
  unless info.all.all (sources.contains ·) do
    throwError "include all mutually recursive syntax inductives that contain {source}"
  let sourceType := info.type.instantiateLevelParams info.levelParams (info.levelParams.map fun _ => .zero)
  forallBoundedTelescope sourceType (some info.numParams) fun params _ => do
    for param in params do
      unless ← isDefEq (← inferType param) (.sort (.succ .zero)) do
        throwError "expected ordinary type parameters in syntax inductive {source}"
  let varCtor := source ++ `var
  let hasVar := info.ctors.contains varCtor
  unless hasVar || family do
    throwError "expected a constructor {varCtor} : String → {source}"
  let mut operators := #[]
  for ctor in info.ctors do
    let ctorInfo ← getConstInfoCtor ctor
    let type := ctorInfo.type.instantiateLevelParams ctorInfo.levelParams
      (ctorInfo.levelParams.map fun _ => .zero)
    let fields ← forallTelescope type fun xs _ => do
      let params := xs.extract 0 info.numParams
      let fields ← (xs.extract info.numParams xs.size).mapM fun x => do
        let field ← x.fvarId!.getDecl
        unless field.binderInfo.isExplicit do
          throwError "expected an explicit field of {ctor}"
        return field
      if ctor == varCtor then
        unless fields.map (·.type) == #[mkConst ``String] do
          throwError "expected {varCtor} : String → {source}"
        return #[]
      fields.mapM fun field => do
        let type := field.type.replaceFVars params parameters
        let kind ← if hasSource sources type then recursiveField sources parameters pattern arity ctor type
          else do
            if (type.find? fun expr => expr.isFVar && !parameters.contains expr).isSome then
              throwError "unsupported dependent field type {type} in {ctor}"
            pure (.payload (← PrettyPrinter.delab type))
        return ⟨field.userName, kind⟩
    unless ctor == varCtor do
      let label := if family then shortName source ++ shortName ctor else shortName ctor
      operators := operators.push ⟨ctor, label, fields⟩
  return ⟨source, hasVar, operators⟩

private structure Parameters where
  args : Array Ident
  explicit : Array (TSyntax ``bracketedBinder)
  implicit : Array (TSyntax ``bracketedBinder)

private def Parameters.apply (params : Parameters) (name : Lean.Name) : CommandElabM Term := do
  let args := params.args
  `(@$(mkIdent name):ident $args*)

private def FieldLayout.quote : FieldLayout → CommandElabM Term
  | .child => `(FieldLayout.child)
  | .list element => do `(FieldLayout.list $(← element.quote))
  | .optional element => do `(FieldLayout.optional $(← element.quote))

private def FieldLayout.valueType (layout : FieldLayout) (element : Term) : CommandElabM Term :=
  match layout with
  | .child => pure element
  | _ => do `(FieldLayout.Values $(← layout.quote) $element)

private def FieldLayout.countExpr (layout : FieldLayout) (shape : Term) : CommandElabM Term :=
  match layout with
  | .child => `(1)
  | _ => do `(FieldLayout.count $(← layout.quote) $shape)

private def addCounts (counts : Array Term) : CommandElabM Term := do
  counts.foldrM (fun count rest => `($count + $rest)) (← `(0))

private def fieldName (kind : Lean.Name) (i : Nat) : Ident :=
  mkIdent (kind.appendIndexAfter i)

private def emitSignature (params : Parameters) (pattern arity : Ident) (operators : Array Operator) :
    CommandElabM Unit := do
  let parameters := params.explicit
  let ctors ← operators.mapM fun op => do
    let mut fields := #[]
    for (field, i) in op.fields.zipIdx do
      match field.kind with
      | .payload type =>
        fields := fields.push (← `(bracketedBinder| ($(mkIdent field.name) : $type)))
      | .recursive _ _ .child => pure ()
      | .recursive _ _ layout =>
        let type ← layout.valueType (← `(Unit))
        fields := fields.push (← `(bracketedBinder| ($(fieldName `shape i) : $type)))
    let label := mkIdent op.label
    let decl ← `(Lean.Parser.Command.optDeclSig| $fields*)
    `(Lean.Parser.Command.ctor| | $label:ident $decl)
  let op := mkIdent `Op
  elabCommand (← `(inductive $op:ident $parameters* where $ctors* deriving DecidableEq))
  let opType ← params.apply `Op
  let arities (countScopes : Bool) : CommandElabM (Array (TSyntax ``matchAlt)) :=
    operators.mapM fun op => do
      let mut counts := #[]
      let mut payloads := #[]
      for (field, i) in op.fields.zipIdx do
        match field.kind with
        | .payload _ => payloads := payloads.push (← `(_))
        | .recursive _ scopedField layout =>
          let shape := fieldName `shape i
          if layout != .child then
            let pattern ← if scopedField == countScopes then `($shape:ident) else `(_)
            payloads := payloads.push pattern
          if scopedField == countScopes then
            counts := counts.push (← layout.countExpr (← `($shape:ident)))
      let arity ← addCounts counts
      `(matchAltExpr| | $(mkIdent op.tag):ident $payloads* => $arity)
  let sig := mkIdent `sig
  let raw := mkIdent `Raw
  let term := mkIdent `Term
  if operators.isEmpty then
    elabCommand (← `(abbrev $sig:ident $parameters* : Signature where
      Op := $opType
      Pattern := $pattern
      terms x := nomatch x
      scopes x := nomatch x
      binders := $arity))
  else
    let terms ← arities false
    let scopes ← arities true
    elabCommand (← `(abbrev $sig:ident $parameters* : Signature where
      Op := $opType
      Pattern := $pattern
      terms := fun $terms:matchAlt*
      scopes := fun $scopes:matchAlt*
      binders := $arity))
  let sigApp ← params.apply `sig
  elabCommand (← `(abbrev $raw:ident $parameters* := Syntax $sigApp String))
  elabCommand (← `(abbrev $term:ident $parameters* := AST $sigApp))

private def finFunction (entries : Array (FieldLayout × Term)) : CommandElabM Term := do
  entries.foldrM (fun (layout, entry) rest => do
    let index ← if layout == .child then `(fun (_ : Fin 1) => $entry) else pure entry
    `(Fin.addCases $index $rest)) (← `(Fin.elim0))

private def emitHelpers (params : Parameters) (operators : Array Operator) (hasVar : Bool) :
    CommandElabM Unit := do
  let parameters := params.implicit
  let sig ← params.apply `sig
  let raw ← params.apply `Raw
  let term ← params.apply `Term
  let termAtScope ← `($term scope)
  if hasVar then
    let rawVar := mkIdent `Raw.var
    let termVar := mkIdent `Term.var
    elabCommand (← `(def $rawVar:ident $parameters* (name : String) : $raw := Syntax.var name))
    elabCommand (← `(def $termVar:ident $parameters* {scope : Scope} (name : Name scope) : $termAtScope :=
      AST.var name))
  for op in operators do
    let mut rawParams := #[]
    let mut termParams := #[]
    let mut rawTerms := #[]
    let mut checkedTerms := #[]
    let mut binders := #[]
    let mut bodies := #[]
    let mut checkedBodies := #[]
    let mut payloads := #[]
    for field in op.fields do
      let arg := mkIdent field.name
      match field.kind with
      | .recursive _ false .child =>
        rawParams := rawParams.push (← `(bracketedBinder| ($arg : $raw)))
        termParams := termParams.push (← `(bracketedBinder| ($arg : $termAtScope)))
        rawTerms := rawTerms.push (.child, ← `($arg:ident))
        checkedTerms := checkedTerms.push (.child, ← `($arg:ident))
      | .recursive _ true .child =>
        let binder := mkIdent (← liftCoreM (mkFreshUserName (field.name.appendAfter "Binder")))
        rawParams := rawParams.push (← `(bracketedBinder| ($binder : Binder $sig String)))
        rawParams := rawParams.push (← `(bracketedBinder| ($arg : $raw)))
        termParams := termParams.push (← `(bracketedBinder| ($arg : ScopedAST $sig scope)))
        binders := binders.push (.child, ← `($binder:ident))
        bodies := bodies.push (.child, ← `($arg:ident))
        checkedBodies := checkedBodies.push (.child, ← `($arg:ident))
      | .recursive _ scopedField layout =>
        let rawChild ← if scopedField then `(Binder $sig String × $raw) else pure raw
        let checkedChild ← if scopedField then `(ScopedAST $sig scope) else pure termAtScope
        let rawType ← layout.valueType rawChild
        let checkedType ← layout.valueType checkedChild
        rawParams := rawParams.push (← `(bracketedBinder| ($arg : $rawType)))
        termParams := termParams.push (← `(bracketedBinder| ($arg : $checkedType)))
        let layoutExpr ← layout.quote
        let rawIndex ← `(FieldLayout.index (α := $rawChild) $layoutExpr $arg)
        let checkedIndex ← `(FieldLayout.index (α := $checkedChild) $layoutExpr $arg)
        payloads := payloads.push
          (← `(FieldLayout.shape (α := $rawChild) $layoutExpr $arg),
           ← `(FieldLayout.shape (α := $checkedChild) $layoutExpr $arg))
        if scopedField then
          binders := binders.push (layout, ← `(fun i => ($rawIndex i).1))
          bodies := bodies.push (layout, ← `(fun i => ($rawIndex i).2))
          checkedBodies := checkedBodies.push (layout, checkedIndex)
        else
          rawTerms := rawTerms.push (layout, rawIndex)
          checkedTerms := checkedTerms.push (layout, checkedIndex)
      | .payload type =>
        let param ← `(bracketedBinder| ($arg : $type))
        rawParams := rawParams.push param
        termParams := termParams.push param
        payloads := payloads.push (← `($arg:ident), ← `($arg:ident))
    let rawPayloads := payloads.map Prod.fst
    let termPayloads := payloads.map Prod.snd
    let rawTag ← `($(mkIdent op.tag):ident $rawPayloads*)
    let termTag ← `($(mkIdent op.tag):ident $termPayloads*)
    let ordinary ← finFunction rawTerms
    let checkedOrdinary ← finFunction checkedTerms
    let patterns ← finFunction binders
    let scopedBodies ← finFunction bodies
    let scopedChecked ← finFunction checkedBodies
    let rawHelper := mkIdent op.rawHelper
    let termHelper := mkIdent (`Term ++ op.label)
    elabCommand (← `(def $rawHelper:ident $parameters* $rawParams* : $raw :=
      Syntax.node ($rawTag) $ordinary $patterns $scopedBodies))
    elabCommand (← `(def $termHelper:ident $parameters* {scope : Scope} $termParams* : $termAtScope :=
      AST.node ($termTag) $checkedOrdinary $scopedChecked))

private def codecName (source direction : Lean.Name) : Ident :=
  mkIdent (shortName source ++ direction)

private def encodeContainer (params : Parameters) (pattern arity : Ident) (child : Lean.Name)
    (scopedField : Bool) (layout : FieldLayout) : CommandElabM (Ident × Array (TSyntax `command)) := do
  let parameters := params.implicit
  let encode := codecName child `toRaw
  if layout == .child && !scopedField then return (encode, #[])
  let source ← params.apply child
  let sig ← params.apply `sig
  let raw ← params.apply `Raw
  let input ← if scopedField then `(BoundSyntax $pattern $arity $source) else pure source
  let output ← if scopedField then `(Binder $sig String × $raw) else pure raw
  let inputType ← layout.valueType input
  let outputType ← layout.valueType output
  let helper := mkIdent (← liftCoreM (mkFreshUserName `encodeField))
  let (body, helpers) ← match layout with
    | .child =>
      pure (← `(match value with
        | ⟨shape, names, length, body⟩ => (⟨shape, names, length⟩, $encode body)), #[])
    | .list element =>
      let (encodeElem, helpers) ← encodeContainer params pattern arity child scopedField element
      pure (← `(match value with
        | [] => []
        | first :: rest => $encodeElem first :: $helper rest), helpers)
    | .optional element =>
      let (encodeElem, helpers) ← encodeContainer params pattern arity child scopedField element
      pure (← `(match value with
        | none => none
        | some item => some ($encodeElem item)), helpers)
  let command ← `(private def $helper:ident $parameters* (value : $inputType) : $outputType :=
    $body)
  return (helper, helpers.push command)

/-- Inject a field's local index into the concatenated child positions. Each cast
follows the constructor helper's right-associated concatenation. -/
private def fieldIndex (op : Operator) (scopedField : Bool) (field : Nat) (index : Term) :
    CommandElabM Term := do
  let mut before := #[]
  let mut after := #[]
  for (entry, i) in op.fields.zipIdx do
    if let .recursive _ entryScoped layout := entry.kind then
      if scopedField == entryScoped && i != field then
        let count ← layout.countExpr (← `($(fieldName `shape i):ident))
        if i < field then before := before.push count else after := after.push count
  let suffix ← addCounts after
  let index ← `(Fin.castAdd $suffix $index)
  before.foldrM (fun count index => `(Fin.natAdd $count $index)) index

private def decodeField (op : Operator) (field : Nat)
    (child : Lean.Name) (scopedField family : Bool) (layout : FieldLayout)
    (terms binders bodies : Ident) : CommandElabM Term := do
  let decode := codecName child `fromRaw
  let index ← if layout == .child then `((0 : Fin 1)) else `(i)
  let index ← fieldIndex op scopedField field index
  let read ← if scopedField then
    if family then
      `((BoundSyntax.ofBinder ($binders $index)) <$> ($decode ($bodies $index)))
    else
      `(BoundSyntax.ofBinder ($binders $index) ($decode ($bodies $index)))
  else
    `($decode ($terms $index))
  if layout == .child then return read
  let layoutExpr ← layout.quote
  let shape := fieldName `shape field
  if family then
    `(FieldLayout.traverse (m := Option) $layoutExpr $shape (fun i => $read))
  else
    `(Id.run (FieldLayout.traverse (m := Id) $layoutExpr $shape (fun i => $read)))

private def emitCodec (params : Parameters) (pattern arity : Ident) (category : Category)
    (family : Bool) : CommandElabM (Array (TSyntax `command) × TSyntax `command) := do
  let parameters := params.implicit
  let raw ← params.apply `Raw
  let decl ← params.apply category.source
  let toRaw := codecName category.source `toRaw
  let fromRaw := codecName category.source `fromRaw
  let mut encodeHelpers := #[]
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
    for (field, i) in op.fields.zipIdx do
      let arg := fieldName `arg i
      match field.kind with
      | .recursive child scopedField layout =>
        if scopedField && layout == .child then
          let encode := codecName child `toRaw
          let shape := fieldName `pattern i
          let names := fieldName `names i
          let length := fieldName `length i
          fields := fields.push (← `(BoundSyntax.mk $shape $names $length $arg))
          toArgs := toArgs.push (← `(⟨$shape, $names, $length⟩))
          toArgs := toArgs.push (← `($encode $arg))
        else
          let (encode, helpers) ← encodeContainer params pattern arity child scopedField layout
          encodeHelpers := encodeHelpers ++ helpers
          fields := fields.push (← `($arg:ident))
          toArgs := toArgs.push (← `($encode $arg))
        if layout != .child then
          payloads := payloads.push (← `($(fieldName `shape i):ident))
        let decoded ← decodeField op i child scopedField family layout terms binders bodies
        if family then
          decoders := decoders.push (arg, decoded)
          fromArgs := fromArgs.push (← `($arg:ident))
        else
          fromArgs := fromArgs.push decoded
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
  else if category.operators.isEmpty then
    fromAlts := fromAlts.push (← `(matchAltExpr| | Syntax.node op _ _ _ => nomatch op))
  let value := mkIdent `value
  let toBody ← if toAlts.isEmpty then `(nomatch $value) else
    `(match $value:ident with $toAlts:matchAlt*)
  let fromBody ← `(match $value:ident with $fromAlts:matchAlt*)
  let result ← if family then `(Option $decl) else pure decl
  let encode ← `(def $toRaw:ident $parameters* ($value : $decl) : $raw := $toBody)
  let decode ← `(def $fromRaw:ident $parameters* ($value : $raw) : $result := $fromBody)
  return (encodeHelpers.push encode, decode)

private def emitResolution (params : Parameters) (source : Lean.Name) (family : Bool) :
    CommandElabM Unit := do
  let parameters := params.implicit
  let term ← params.apply `Term
  let decl ← params.apply source
  let sig ← params.apply `sig
  let toRaw := codecName source `toRaw
  let fromRaw := codecName source `fromRaw
  let resolve := codecName source `resolve
  let resolveClosed := codecName source `resolveClosed
  let toDeclaration := mkIdent (Lean.Name.str `Term ("to" ++ source.getString!))
  let result ← if family then `(Option $decl) else pure decl
  elabCommand (← `(def $resolve:ident $parameters* (scope : Scope)
      (lookup : String → Option (Name scope)) (value : $decl) :
      Except (ResolveError String) ($term scope) :=
    AST.fromNamed (sig := $sig) scope lookup ($toRaw value)))
  elabCommand (← `(def $resolveClosed:ident $parameters* (value : $decl) :
      Except (ResolveError String) ($term []) :=
    AST.fromClosed ($toRaw value)))
  elabCommand (← `(def $toDeclaration:ident $parameters* (scope : Scope) (value : $term scope)
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
  let parameterCount ← liftTermElabM do
    let info ← getConstInfoInduct sources[0]!
    pure info.numParams
  let paramNames ← liftCoreM <| (Array.range parameterCount).mapM fun _ => mkFreshUserName `parameter
  let args := paramNames.map mkIdent
  let explicit ← args.mapM fun arg => `(bracketedBinder| ($arg : Type))
  let implicit ← args.mapM fun arg => `(bracketedBinder| {$arg : Type})
  let params : Parameters := ⟨args, explicit, implicit⟩
  let categories ← liftTermElabM <| withLocalDeclsDND (paramNames.map fun name =>
    (name, .sort (.succ .zero))) fun parameters => sources.mapM fun source =>
      readCategory sources family parameters patternName arityName source
  let operators := categories.flatMap (·.operators)
  let pattern := mkIdent patternName
  let arity := mkIdent arityName
  emitSignature params pattern arity operators
  emitHelpers params operators (categories.any (·.hasVar))
  let codecs ← categories.mapM fun category => emitCodec params pattern arity category family
  let encoders := codecs.flatMap Prod.fst
  let decoders := codecs.map Prod.snd
  if encoders.size == 1 then
    elabCommand encoders[0]!
  else
    elabCommand (← `(mutual $encoders* end))
  if family then
    elabCommand (← `(mutual $decoders* end))
  else
    for decode in decoders do
      elabCommand decode
  for source in sources do
    emitResolution params source family

/-- Derive `Op`, `sig`, `Raw`, `Term`, and their constructors and conversions.
The source inductive has a `var` constructor taking a `String`. Other constructors take
ordinary or scoped recursive fields, optionally nested in lists and options, or fixed payloads. -/
elab "derive_free_foil " source:ident " with " pattern:ident ", " arity:ident : command =>
  deriveFamily #[source] pattern arity false

/-- Derive a shared Free Foil signature for several syntax categories. Each category
has its own constructor namespace and codecs. Decoding from the common representation
checks that a tree uses the requested category and the declared categories of its children. -/
elab "derive_free_foil " "[" sources:ident,+ "]" " with " pattern:ident ", " arity:ident : command =>
  deriveFamily sources.getElems pattern arity true

end Derive
end FreeFoil

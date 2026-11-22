import FreeFoil.Examples.MLTT

namespace FreeFoil.Tests.MLTT

open Examples.MLTT

private def verify (message : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError message)

private def expectOk [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def term (source : String) : IO (Term []) := do
  AST.fromClosed (← expectOk (Parser.parseTerm source)) |> expectOk

-- The examples here follow upstream Language.MLTT.ImplSpec at fdfbeef.
private def bidirectionalTests : IO Unit := do
  let ctx := Context.empty
  let polymorphic ← term "Π (A : 𝕌) → A → A"
  expectOk (check ctx 128 (← term "λ A x ⇒ x") polymorphic)
  let dependentPair ← term "Π (p : Σ (A : 𝕌) × A) → π₁ p"
  expectOk (check ctx 128 (← term "λ (A, x) ⇒ x") dependentPair)
  expectOk (check ctx 128 (← term "λ _ ⇒ tt") (← term "Π (A : 𝕌) → 𝟙"))
  let inferred ← expectOk (infer ctx 128 (← term "π₂ (𝟙, tt)"))
  verify "MLTT inferred the wrong type for the dependent projection"
    (inferred.alphaEquiv Term.unitType)
  let annotated ← term "(λ x ⇒ x : 𝟙 → 𝟙) tt"
  verify "MLTT could not infer the type of an ascribed lambda application"
    ((← expectOk (infer ctx 128 annotated)).alphaEquiv Term.unitType)

  let invalidArg ← term "(λ x ⇒ x : 𝟙 → 𝟙) 𝕌"
  verify "MLTT accepted an argument of the wrong type" (infer ctx 128 invalidArg).toOption.isNone
  let bareLambda ← term "λ x ⇒ x"
  verify "MLTT inferred a bare lambda" (infer ctx 128 bareLambda).toOption.isNone
  verify "MLTT checked a lambda against a non-Π type"
    (check ctx 128 bareLambda Term.unitType).toOption.isNone

  -- The upstream rule checks uses of a pattern by inserting its projections.
  let nonPairDomain ← term "𝟙 → 𝟙"
  expectOk (check ctx 128 (← term "λ (x, y) ⇒ tt") nonPairDomain)
  verify "MLTT accepted a projection from a non-Σ input"
    (check ctx 128 (← term "λ (x, y) ⇒ x") nonPairDomain).toOption.isNone
  let value ← term "let (x, _) = (tt, 𝟙) in x"
  verify "MLTT inferred the wrong type for a pattern let"
    ((← expectOk (infer ctx 128 value)).alphaEquiv Term.unitType)
  verify "MLTT failed to evaluate a pattern let"
    ((← expectOk (nf [] ctx.definitions 128 value)).alphaEquiv Term.unitVal)

private def conversionTests : IO Unit := do
  let agrees (lhs rhs : String) : IO Bool := do
    expectOk (conv [] Context.empty.definitions 128 (← term lhs) (← term rhs))
  verify "MLTT conversion missed beta reduction" (← agrees "(λ x ⇒ x) tt" "tt")
  verify "MLTT conversion compared binder names" (← agrees "λ x ⇒ x" "λ y ⇒ y")
  verify "MLTT conversion missed eta contraction" (← agrees "λ f ⇒ λ x ⇒ f x" "λ f ⇒ f")
  verify "MLTT conversion accepted unequal normal forms" (!(← agrees "λ x ⇒ x" "λ x ⇒ tt"))
  verify "MLTT conversion confused distinct pair-pattern bindings"
    (!(← agrees "λ (x, _) ⇒ x" "λ (_, y) ⇒ y"))
  let loop ← term "(λ x ⇒ x x) (λ x ⇒ x x)"
  match nf [] Context.empty.definitions 8 loop with
  | .error .outOfFuel => pure ()
  | .ok _ => throw (IO.userError "MLTT normalized a diverging term within its fuel budget")

private def contextTests : IO Unit := do
  let scope : Scope := [7, 11]
  let old : Name [11] := ⟨11, by decide⟩
  let x : Name scope := ⟨11, by decide⟩
  let assumption := Context.empty.extend 11 (by decide) Term.unitType
  let ctx : Context scope :=
    assumption.extend 7 (by decide) Term.unitType (some (Term.var old))
  let dependency : Name (11 :: scope) := ⟨7, by decide⟩
  let binding := Term.lam (variableBody 11 (Term.var dependency))
  let normal ← expectOk (nf scope ctx.definitions 128 binding)
  verify "MLTT unfolding below a sunk binder captured a free name" (normal.freeVars == [11])
  verify "MLTT lost the type of an explicitly allocated name"
    ((← expectOk (infer ctx 128 (Term.var x))).alphaEquiv Term.unitType)
  let etaBlocker ← term "λ x ⇒ x x"
  let inScope := etaBlocker.sink (by simp : [] ⊆ [0])
  let neutral := Context.empty.extend 0 (by decide) Term.unitType
  let normal ← expectOk (nf [0] neutral.definitions 128 inScope)
  verify "MLTT treated a shadowed ambient name as an eta contraction" (normal.alphaEquiv inScope)

private def programTests : IO Unit := do
  let source ← IO.FS.readFile "test/fixtures/mltt/core.mltt"
  let program ← expectOk (Parser.parseProgram source)
  verify "MLTT core fixture lost its module name" (program.moduleName == some "Core")
  let results ← expectOk ((runProgram program).mapM id)
  let definitions := results.filterMap fun
    | .defined name => some name
    | _ => none
  let checked := results.filter fun
    | .checked _ _ => true
    | _ => false
  let computed := results.filterMap fun
    | .computed result => some result
    | _ => none
  verify "MLTT core fixture lost a checked definition"
    (definitions == #["id", "compose", "snd", "transport"])
  verify "MLTT core fixture lost a check" (checked.size == 2)
  verify "MLTT core fixture reduced a command incorrectly" (computed == #["tt", "tt", "tt", "tt"])

  let source := "module Errors\n\
    def good : 𝟙 := tt\n\
    def good : 𝕌 := 𝕌\n\
    def bad : 𝟙 := 𝕌\n\
    compute bad\n\
    compute good"
  let results := runProgram (← expectOk (Parser.parseProgram source))
  match results with
  | #[.ok (.defined "good"), .error duplicate, .error _, .error unbound, .ok (.computed "tt")] =>
    verify "MLTT reported the wrong error for a duplicate definition" (duplicate.startsWith "duplicate")
    verify "MLTT installed an ill-typed definition" (unbound.startsWith "unbound")
  | _ => throw (IO.userError (reprStr results))

private def singleModule (source : String) : IO Module := do
  let #[mod] ← expectOk (Parser.parseModules source)
    | throw (IO.userError "expected one MLTT module")
  pure mod

private def expectError (fragment : String) (result : Except String α) : IO Unit :=
  match result with
  | .error message =>
    verify s!"expected '{fragment}' in MLTT error '{message}'" (message.contains fragment)
  | .ok _ => throw (IO.userError s!"expected MLTT error containing '{fragment}'")

private def parameterTests : IO Unit := do
  let source ← IO.FS.readFile "test/fixtures/mltt/parameters.mltt"
  let modules ← expectOk (Parser.parseModules source)
  let results ← expectOk (runModules modules)
  let computed := (results.flatMap Prod.snd).filterMap fun
    | .computed result => some result
    | _ => none
  verify "the upstream MLTT parameter example reduced a command incorrectly"
    (computed == #["tt", "tt", "tt", "tt", "tt"])
  let wrongOver ← singleModule
    "module Wrong (A : 𝕌) (x : A) def item over (x) : A := x"
  expectError "uses over (A, x)" (checkModule .empty ⟨0, 1⟩ wrongOver)
  let dupParam ← singleModule "module Wrong (A : 𝕌) (A : 𝕌)"
  expectError "duplicate parameter" (checkModule .empty ⟨0, 1⟩ dupParam)
  let badParam ← singleModule "module Wrong (a : tt)"
  expectError "expected type" (checkModule .empty ⟨0, 1⟩ badParam)
  let client ← singleModule "module Top import Dep compute Dep.result"
  let dep ← singleModule "module Dep def result : 𝟙 := tt"
  verify "MLTT did not build modules in dependency order"
    (((← expectOk (runModules #[client, dep])).map Prod.fst) == #["Dep", "Top"])
  expectError "missing dependency 'Dep'" (runModules #[client])
  let cyclic ← singleModule "module Dep import Top"
  expectError "cyclic module imports" (runModules #[client, cyclic])

private def namedTelescopeTests : IO Unit := do
  let source := "telescope Params include Carrier include Spare (x : A);\n\
    module Left include Params (y : A);\n\
    def item over (A, y) : A := y;\n\
    telescope Carrier (A : 𝕌);\n\
    telescope Spare (spare : 𝟙);\n\
    module Right include Params;\n\
    def item over (A, x) : A := x;\n\
    module Client import Left import Right\n\
    compute Left.item 𝟙 tt\n\
    compute Right.item 𝟙 tt"
  let .modules modules ← expectOk (Parser.parseInput source)
    | throw (IO.userError "telescope source did not parse as MLTT modules")
  let #[left, right, _] := modules
    | throw (IO.userError "telescope declarations appeared as MLTT modules")
  verify "MLTT did not place included fields in order before local fields"
    (left.parameters.map Parameter.name == #["A", "spare", "x", "y"] &&
      right.parameters.map Parameter.name == #["A", "spare", "x"])
  let results ← expectOk (runModules modules)
  verify "MLTT did not compute through both independently elaborated telescope headers"
    (results.back? == some ("Client", #[.computed "tt", .computed "tt"]))
  let explicit ← singleModule
    "module Left (A : 𝕌) (spare : 𝟙) (x : A) (y : A) def item over (A, y) : A := y"
  let (included, _) ← expectOk (checkModule .empty ⟨10, 20⟩ left)
  let (written, _) ← expectOk (checkModule .empty ⟨10, 20⟩ explicit)
  let _ ← expectOk (linkModules included written)
  let importedTypes ← expectOk (Parser.parseModules
    "telescope Imported (x : U)\n\
    module UnitType def U : 𝕌 := 𝟙\n\
    module Universe def U : 𝕌 := 𝕌\n\
    module UnitUser include Imported import UnitType def chosen : U := x\n\
    module UniverseUser include Imported import Universe def chosen : U := x\n\
    module ImportClient import UnitUser import UniverseUser\n\
    compute UnitUser.chosen tt\n\
    compute UniverseUser.chosen 𝟙")
  let results ← expectOk (runModules importedTypes)
  verify "MLTT did not resolve telescope fields in each module's import scope"
    (results.back? == some ("ImportClient", #[.computed "tt", .computed "𝟙"]))
  expectError "missing telescope 'Missing' in module 'Client'"
    (Parser.parseModules "module Client include Missing")
  expectError "missing telescope 'Missing'"
    (Parser.parseModules "telescope T include Missing")
  expectError "cyclic telescope includes: A -> B -> A"
    (Parser.parseModules "telescope A include B telescope B include A")
  expectError "duplicate telescope 'T'"
    (Parser.parseModules "telescope T telescope T")
  expectError "duplicate parameter 'A' in telescope 'Both'"
    (Parser.parseModules "telescope T (A : 𝕌) telescope Both include T include T")
  expectError "duplicate parameter 'A' in module 'Client'"
    (Parser.parseModules "telescope T (A : 𝕌) module Client include T (A : 𝕌)")

private def moduleLinkTests : IO Unit := do
  let common ← singleModule "module Common def base : 𝟙 := tt def U : 𝕌 := 𝟙"
  let left ← singleModule "module Left (A : 𝕌) (x : A) (unused : 𝟙) import Common\n\
    def first : A := x\n\
    def left over (x, A) : A := first\n\
    def common : 𝟙 := base"
  let right ← singleModule "module Right (x : U) import Common def right : U := x"
  let client ← singleModule "module Client import Left import Right\n\
    compute Right.right (Left.left 𝟙 Left.common)"
  let (base, _) ← expectOk (checkModule .empty ⟨10, 20⟩ common)
  let (a, _) ← expectOk (checkModule base ⟨100, 110⟩ left)
  let (b, _) ← expectOk (checkModule base ⟨50, 60⟩ right)
  for linked in [linkModules a b, linkModules b a] do
    let linked ← expectOk linked
    let names (moduleName : String) : List (Nat × List String) :=
      ((linked.find? moduleName).map (·.declarations)).getD [] |>.map fun decl =>
        (decl.key.id, decl.parameters)
    verify "linking renamed or duplicated a declaration"
      (names "Left" == [(100, ["A", "x"]), (101, ["A", "x"]), (102, [])] &&
        names "Right" == [(50, ["x"])] && names "Common" == [(10, []), (11, [])] &&
        linked.scope.Nodup)
    let (_, results) ← expectOk (checkModule linked ⟨150, 160⟩ client)
    verify "a linked client could not compute through both imports"
      (results == #[.computed "tt"])
    let hidden ← singleModule "module Client import Left import Right compute base"
    expectError "unbound name 'base'" (checkModule linked ⟨150, 160⟩ hidden)
    let transient ← singleModule "module Client import Left compute Left.unused"
    expectError "unbound name 'Left.unused'" (checkModule linked ⟨150, 160⟩ transient)

  expectError "invalid reserved name range" (checkModule base ⟨20, 20⟩ left)
  expectError "invalid reserved name range" (checkModule base ⟨55, 54⟩ right)
  expectError "range exhausted" (checkModule base ⟨30, 32⟩ left)
  expectError "ranges overlap" (checkModule base ⟨12, 13⟩ right)
  let (unusedRange, _) ← expectOk (checkModule base ⟨109, 111⟩ right)
  expectError "ranges overlap" (linkModules a unusedRange)
  let emptyA ← singleModule "module EmptyA"
  let emptyB ← singleModule "module EmptyB"
  let (emptyLeft, _) ← expectOk (checkModule base ⟨40, 42⟩ emptyA)
  let (emptyRight, _) ← expectOk (checkModule base ⟨41, 43⟩ emptyB)
  expectError "ranges overlap" (linkModules emptyLeft emptyRight)
  let conflicting ← singleModule
    "module Common def base : 𝟙 := (λ x ⇒ x : 𝟙 → 𝟙) tt def U : 𝕌 := 𝟙"
  let (changedBase, _) ← expectOk (checkModule .empty ⟨10, 20⟩ conflicting)
  let (changedBranch, _) ← expectOk (checkModule changedBase ⟨50, 60⟩ right)
  expectError "conflicting checked copies of module 'Common'" (linkModules a changedBranch)
  let withImport ← singleModule "module EmptyA import Common"
  let (changedImports, _) ← expectOk (checkModule base ⟨40, 42⟩ withImport)
  expectError "conflicting checked copies of module 'EmptyA'" (linkModules emptyLeft changedImports)

private def importResolutionTests : IO Unit := do
  let left ← singleModule "module Left def shared : 𝟙 := tt def Nested.name : 𝟙 := tt"
  let right ← singleModule "module Left.Nested def shared : 𝟙 := tt def name : 𝟙 := tt"
  let (env, _) ← expectOk (checkModule .empty ⟨0, 2⟩ left)
  let (env, _) ← expectOk (checkModule env ⟨2, 4⟩ right)
  let header := "module Client import Left import Left.Nested "
  let ambiguous ← singleModule (header ++ "compute shared")
  expectError "ambiguous name 'shared'" (checkModule env ⟨4, 5⟩ ambiguous)
  let qualified ← singleModule (header ++ "compute Left.Nested.name")
  expectError "ambiguous name 'Left.Nested.name'" (checkModule env ⟨4, 5⟩ qualified)
  let client ← singleModule (header ++ "def shared : 𝟙 := Left.shared compute shared")
  let (_, results) ← expectOk (checkModule env ⟨4, 5⟩ client)
  verify "an import collision hid a local definition or qualified name"
    (results == #[.defined "shared", .computed "tt"])
  let binder ← singleModule (header ++ "compute (λ shared ⇒ shared : 𝟙 → 𝟙) tt")
  let (_, results) ← expectOk (checkModule env ⟨4, 5⟩ binder)
  verify "an import collision hid a lexical binder" (results == #[.computed "tt"])
  let parameter ← singleModule "module Client (shared : 𝟙) import Left import Left.Nested\n\
    def value over (shared) : 𝟙 := shared"
  let (_, results) ← expectOk (checkModule env ⟨4, 5⟩ parameter)
  verify "an import collision hid a parameter" (results == #[.defined "value"])

private def loadEncoded (env : CheckedModules) (artifact : ModuleArtifact) :
    Except String CheckedModules := do
  loadArtifact env (← decodeArtifact (encodeArtifact artifact))

private def updateArtifactDeclaration (artifact : ModuleArtifact) (index : Nat)
    (update : ArtifactDeclaration → ArtifactDeclaration) : ModuleArtifact :=
  let declarations := artifact.payload.declarations.modify index update
  { artifact with payload := { artifact.payload with declarations } }

private def setArtifactValue (artifact : ModuleArtifact) (value : Lean.Json) : ModuleArtifact :=
  updateArtifactDeclaration artifact 0 fun decl => { decl with value }

private def artifactTests : IO Unit := do
  let common ← singleModule "module Common def U : 𝕌 := 𝟙 def base : U := tt"
  let left ← singleModule "module Left (x : U) import Common\n\
    def choose : U := x\n\
    def again : U := choose\n\
    def base : U := Common.base"
  let right ← singleModule "module Right import Common\n\
    def rotate : (𝕌 × (𝕌 × 𝕌)) → (𝕌 × (𝕌 × 𝕌)) := λ (A, (B, C)) ⇒ (C, (A, B))"
  let client ← singleModule "module Client import Left import Right\n\
    compute Left.again Left.base\n\
    compute π₁ (Right.rotate (𝟙, (𝕌, Id(𝟙, tt, tt))))\n\
    compute π₁ (π₂ (Right.rotate (𝟙, (𝕌, Id(𝟙, tt, tt)))))\n\
    compute π₂ (π₂ (Right.rotate (𝟙, (𝕌, Id(𝟙, tt, tt)))))"
  let (base, _) ← expectOk (checkModule .empty ⟨0, 10⟩ common)
  let (checkedLeft, _) ← expectOk (checkModule base ⟨100, 110⟩ left)
  let (checkedRight, _) ← expectOk (checkModule base ⟨20, 30⟩ right)
  let baseArtifact ← expectOk (makeArtifact base "Common")
  let leftArtifact ← expectOk (makeArtifact checkedLeft "Left")
  let rightArtifact ← expectOk (makeArtifact checkedRight "Right")
  let restoredBase ← expectOk (loadEncoded .empty baseArtifact)
  let restoredLeft ← expectOk (loadEncoded restoredBase leftArtifact)
  let restoredRight ← expectOk (loadEncoded restoredBase rightArtifact)
  let linked ← expectOk (linkModules restoredLeft restoredRight)
  let (_, results) ← expectOk (checkModule linked ⟨200, 210⟩ client)
  verify "an artifact round trip changed the client computations or nested binder order"
    (results == #[.computed "tt", .computed "Id(𝟙, tt, tt)", .computed "𝟙", .computed "𝕌"])
  let _ ← expectOk (linkModules restoredLeft checkedLeft)
  for artifact in [baseArtifact, leftArtifact, rightArtifact] do
    let stored ← expectOk (makeArtifact linked artifact.payload.name)
    verify "re-export changed the artifact of a loaded declaration"
      (encodeArtifact stored == encodeArtifact artifact)

  let foreignMod ← singleModule "module Foreign def secret : 𝟙 := tt"
  let (expanded, _) ← expectOk (checkModule restoredBase ⟨400, 410⟩ foreignMod)
  let (checkedExpanded, _) ← expectOk (checkModule expanded ⟨100, 110⟩ left)
  let expandedArtifact ← expectOk (makeArtifact checkedExpanded "Left")
  verify "unrelated declarations affected artifact bytes"
    (encodeArtifact expandedArtifact == encodeArtifact leftArtifact)
  let _ ← expectOk (loadEncoded expanded leftArtifact)

  expectError "missing dependency 'Common'" (loadEncoded .empty leftArtifact)
  let changed ← singleModule "module Common def U : 𝕌 := 𝟙 def base : U := (tt : U)"
  let (changedBase, _) ← expectOk (checkModule .empty ⟨0, 10⟩ changed)
  expectError "dependency manifest" (loadEncoded changedBase leftArtifact)
  let (changedLeft, _) ← expectOk (checkModule changedBase ⟨100, 110⟩ left)
  let child ← singleModule "module Child import Left def exposed : 𝟙 := Left.base"
  let (checkedChild, _) ← expectOk (checkModule checkedLeft ⟨300, 310⟩ child)
  let childArtifact ← expectOk (makeArtifact checkedChild "Child")
  expectError "dependency manifest" (loadEncoded changedLeft childArtifact)

  let global (id : Nat) := Lean.Json.arr #[.str "free", Lean.toJson id]
  expectError "unavailable global identifier 1"
    (loadEncoded checkedLeft (setArtifactValue childArtifact (global 1)))
  expectError "unavailable global identifier 101"
    (loadEncoded restoredBase (setArtifactValue leftArtifact (global 101)))
  expectError "unavailable global identifier 400"
    (loadEncoded expanded (setArtifactValue leftArtifact (global 400)))
  expectError "unbound lexical level 0"
    (loadEncoded restoredBase (setArtifactValue leftArtifact (.arr #[.str "bound", Lean.toJson (0 : Nat)])))
  let noChildren := Lean.Json.arr #[.str "node", Lean.toJson Op.lam, .arr #[], .arr #[]]
  expectError "wrong scoped child arity" (loadEncoded restoredBase (setArtifactValue leftArtifact noChildren))
  let wrongType := Lean.Json.arr #[.str "node", Lean.toJson Op.univ, .arr #[], .arr #[]]
  expectError "expected type" (loadEncoded checkedLeft (setArtifactValue childArtifact wrongType))
  let badId := updateArtifactDeclaration leftArtifact 1 fun decl => { decl with id := 100 }
  expectError "invalid declaration identifier" (loadEncoded restoredBase badId)
  let badRange := { leftArtifact with payload := { leftArtifact.payload with range := ⟨110, 100⟩ } }
  expectError "invalid reserved name range" (loadEncoded restoredBase badRange)
  let shortRange := { leftArtifact with payload := { leftArtifact.payload with range := ⟨100, 101⟩ } }
  expectError "invalid declaration identifier" (loadEncoded restoredBase shortRange)
  let (blocker, _) ← expectOk (checkModule restoredBase ⟨109, 111⟩ foreignMod)
  expectError "reserved name ranges overlap" (loadEncoded blocker leftArtifact)
  expectError "duplicate module 'Left'" (loadEncoded restoredLeft leftArtifact)
  expectError "unsupported MLTT artifact version"
    (decodeArtifact ((encodeArtifact leftArtifact).replace "\"version\":1" "\"version\":2"))

def run : IO Unit := do
  bidirectionalTests
  conversionTests
  contextTests
  programTests
  parameterTests
  namedTelescopeTests
  moduleLinkTests
  importResolutionTests
  artifactTests

end FreeFoil.Tests.MLTT

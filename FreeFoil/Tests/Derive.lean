import FreeFoil.Alpha
import FreeFoil.Derive

namespace FreeFoil.Tests.Derive

private def arity (shape : Nat) : Nat := shape

private def check (message : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError message)

namespace Single

inductive Source (Literal : Type u) (Label : Type v) where
  | var (name : String)
  | literal (value : Literal)
  | collect (first : Source Literal Label) (label : Label)
      (rest : List (Option (Source Literal Label))) (last : Source Literal Label)

derive_free_foil Source with Nat, arity

example {Literal Label : Type} [DecidableEq Literal] [DecidableEq Label] :
    DecidableEq (Op Literal Label) := inferInstance

def run : IO Unit := do
  let raw : Raw Nat String :=
    Raw.collect (Raw.literal 1) "items" [none, some (Raw.literal 2), none] (Raw.literal 3)
  let .collect (.literal 1) "items" [none, some (.literal 2), none] (.literal 3) :=
    Source.fromRaw raw | throw (IO.userError "the single codec changed a list element or lost a payload")
  let .ok original := AST.fromClosed raw
    | throw (IO.userError "could not resolve the nested literal fixture")
  let .ok roundTrip := Source.resolveClosed (Source.fromRaw raw)
    | throw (IO.userError "could not resolve the decoded literal fixture")
  check "the parameterized codec changed the syntax" (original.alphaEquiv roundTrip)
  let different := Term.collect (Term.literal 1) "items" [some (Term.literal 2)] (Term.literal 3)
  check "operator equality ignored option positions" (!original.alphaEquiv different)

end Single

namespace Family

mutual
inductive SourceTerm (Literal : Type) where
  | var (name : String)
  | literal (value : Literal)
  | ascribe (term : SourceTerm Literal) (types : List (Option (SourceType Literal)))

inductive SourceType (Literal : Type) where
  | using (terms : Option (List (BoundSyntax Nat arity (SourceTerm Literal))))
end

derive_free_foil [SourceTerm, SourceType] with Nat, arity

def run : IO Unit := do
  let fields : List (BoundSyntax Nat arity (SourceTerm Nat)) :=
    [⟨1, ["x"], rfl, .var "x"⟩, ⟨1, ["y"], rfl, .var "y"⟩]
  let source := SourceTerm.ascribe (.literal 7) [none, some (.using (some fields))]
  let some (.ascribe (.literal 7) [none, some (.using (some
    [⟨1, ["x"], _, .var "x"⟩, ⟨1, ["y"], _, .var "y"⟩]))]) := SourceTerm.fromRaw source.toRaw
    | throw (IO.userError "the family codec changed the order of scoped children")
  let .ok original := SourceTerm.resolveClosed source
    | throw (IO.userError "nested binders were invisible in their own bodies")
  let some named := Term.toSourceTerm [] original (fun name => nomatch name.property)
    | throw (IO.userError "the scoped codec rejected its own encoding")
  let .ok roundTrip := SourceTerm.resolveClosed named
    | throw (IO.userError "the nested round trip lost a binder")
  check "the nested round trip changed binding structure" (original.alphaEquiv roundTrip)

  let wrongScope := SourceType.using (some (fields ++ [⟨1, ["z"], rfl, .var "y"⟩]))
  let .error (.unbound "y") := SourceType.resolveClosed wrongScope
    | throw (IO.userError "a nested binder leaked into a sibling's scope")
  let badType := Raw.SourceTerm.ascribe (Raw.SourceTerm.literal 7)
    [none, some (Raw.SourceTerm.literal 8)]
  check "decoder accepted the wrong category inside an ordinary container"
    (SourceTerm.fromRaw badType).isNone
  let emptyType : Raw Nat := Raw.SourceType.usingScoped none
  let malformed := Raw.SourceType.usingScoped (some [(⟨0, [], rfl⟩, emptyType)])
  check "decoder accepted the wrong category inside a scoped container"
    (SourceType.fromRaw malformed).isNone

end Family

namespace Unsupported

inductive Source where
  | var (name : String)
  | array (entries : Array Source)

/--
error: unsupported recursive field type Array Source in FreeFoil.Tests.Derive.Unsupported.Source.array; use List, Option, or BoundSyntax
-/
#guard_msgs (whitespace := lax) in
derive_free_foil Source with Nat, arity

inductive Indexed : Nat → Type where
  | var (name : String) : Indexed 0

/-- error: indexed syntax inductive FreeFoil.Tests.Derive.Unsupported.Indexed is unsupported -/
#guard_msgs in
derive_free_foil Indexed with Nat, arity

inductive Sized (n : Nat) where
  | var (name : String)

/-- error: expected ordinary type parameters in syntax inductive FreeFoil.Tests.Derive.Unsupported.Sized -/
#guard_msgs in
derive_free_foil Sized with Nat, arity

end Unsupported

def run : IO Unit := do
  Single.run
  Family.run

end FreeFoil.Tests.Derive

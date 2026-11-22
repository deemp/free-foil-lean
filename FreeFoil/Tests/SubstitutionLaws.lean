import FreeFoil.SubstitutionLaws

namespace FreeFoil.Tests.SubstitutionLaws

private abbrev exampleSig : Signature where
  Op := Bool
  Pattern := Unit
  terms isBinder := if isBinder then 0 else 2
  scopes isBinder := if isBinder then 1 else 0
  binders _ := 2

private def pair (left right : AST exampleSig scope) : AST exampleSig scope :=
  .node false (Fin.cases left (fun _ => right)) Fin.elim0

private def bindPair (first second : Nat) (distinct : first ≠ second)
    (body : AST exampleSig (first :: second :: scope)) : AST exampleSig scope :=
  .node true Fin.elim0 (fun _ => ⟨⟨(), [first, second], rfl⟩, by simp [distinct], body⟩)

private def openTerm : AST exampleSig [0] :=
  bindPair 1 2 (by decide) (pair (.var ⟨0, by simp⟩) (.var ⟨2, by simp⟩))

private def first : Substitution exampleSig [0] [1] :=
  .mapping fun _ => .var ⟨1, by simp⟩

private def second : Substitution exampleSig [1] [2, 5] :=
  .mapping fun _ => bindPair 7 8 (by decide) (pair (.var ⟨2, by simp⟩) (.var ⟨8, by simp⟩))

private def sequential : AST exampleSig [2, 5] :=
  (openTerm.substitute [1] first).substitute [2, 5] second

private def composed : AST exampleSig [2, 5] :=
  openTerm.substitute [2, 5] (first.compose second)

private def patternNames (term : AST exampleSig scope) : List Nat :=
  match term.view with
  | .node true _ children => (children ⟨0, by decide⟩).binder.names
  | _ => []

private def shadowingTerm : AST exampleSig [1, 0] := openTerm.sink (by simp)

example : patternNames (shadowingTerm.substitute [1, 0] (.mapping AST.var)) = [2, 3] := by decide
example : (shadowingTerm.substitute [1, 0] (.mapping AST.var)).alphaEquiv shadowingTerm = true :=
  shadowingTerm.substitute_explicitIdentity

example : patternNames sequential = [6, 3] ∧ patternNames composed = [1, 6] := by decide
example : sequential.freeVars = [2] ∧ composed.freeVars = [2] := by decide
example : sequential.alphaEquiv composed = true := openTerm.substitute_compose first second
example : sequential.alphaEquiv composed = true := by decide
example : (openTerm.substitute [0] .identity).alphaEquiv openTerm = true :=
  openTerm.substitute_identity
example : (openTerm.refresh [0]).alphaEquiv openTerm = true := openTerm.refresh_alphaEquiv
example :
    ((openTerm.substituteRefreshed [1] first).substituteRefreshed [2, 5] second).alphaEquiv
      composed = true :=
  openTerm.substituteRefreshed_compose first second

private def lexical (term : AST exampleSig scope) : Lexical exampleSig :=
  Lexical.interpret term.syntaxTree 0 Lexical.freeAssignment

private def shadowedPair : AST exampleSig [0] :=
  bindPair 1 2 (by decide) (bindPair 1 3 (by decide)
    (pair (.var ⟨1, by simp⟩) (.var ⟨0, by simp⟩)))

private def renamedPair : AST exampleSig [0] :=
  bindPair 4 5 (by decide) (bindPair 6 7 (by decide)
    (pair (.var ⟨6, by simp⟩) (.var ⟨0, by simp⟩)))

example : lexical shadowedPair = lexical renamedPair :=
  (shadowedPair.alphaEquiv_iff_lexical_eq renamedPair).mp (by decide)

private def freeUse (name : Name [0, 9]) : AST exampleSig [0, 9] :=
  bindPair 1 2 (by decide) (.var ⟨name.id, by simp [name.property]⟩)

example : lexical (freeUse ⟨0, by simp⟩) ≠ lexical (freeUse ⟨9, by simp⟩) :=
  mt (AST.alphaEquiv_iff_lexical_eq (freeUse ⟨0, by simp⟩) (freeUse ⟨9, by simp⟩)).mpr (by decide)

private def firstPosition : AST exampleSig [0] :=
  bindPair 1 2 (by decide) (pair (.var ⟨0, by simp⟩) (.var ⟨1, by simp⟩))

example : lexical openTerm ≠ lexical firstPosition :=
  mt (openTerm.alphaEquiv_iff_lexical_eq firstPosition).mpr (by decide)

end FreeFoil.Tests.SubstitutionLaws

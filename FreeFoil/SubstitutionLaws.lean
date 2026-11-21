import FreeFoil.Alpha

namespace FreeFoil.AST

variable {sig : Signature} {source middle target : Scope}

private theorem interpret_compose (term : AST sig source) (first : Substitution sig source middle)
    (second : Substitution sig middle target) (depth : Nat) (env : Lexical.Assignment sig) :
    Lexical.interpret term.syntaxTree depth (first.interpret (second.interpret env)) =
      Lexical.interpret term.syntaxTree depth ((first.compose second).interpret env) := by
  apply Lexical.interpret_congr _ term.wellScoped
  intro id mem current
  simpa [Substitution.interpret, mem, Substitution.compose, Substitution.lookup] using
    (interpret_substitute (first.lookup ⟨id, mem⟩) second current env).symm

private theorem interpret_identity (term : AST sig source)
    (subst : Substitution sig source source) (lookupVar : ∀ name, subst.lookup name = .var name) :
    Lexical.interpret term.syntaxTree 0 (subst.interpret Lexical.freeAssignment) =
      Lexical.interpret term.syntaxTree 0 Lexical.freeAssignment := by
  apply Lexical.interpret_congr _ term.wellScoped
  intro id mem current
  simp only [Substitution.interpret, mem, dite_eq_left]
  rw [lookupVar ⟨id, mem⟩]
  rfl

variable [DecidableEq sig.Op] [DecidableEq sig.Pattern]

/-- The identity substitution preserves every term up to α-equivalence. -/
theorem substitute_identity (term : AST sig source) :
    (term.substitute source .identity).alphaEquiv term = true :=
  alphaEquiv_of_lexical_eq _ _ rfl

/-- The identity law also holds for an explicit variable map, which traverses the term. -/
theorem substitute_explicitIdentity (term : AST sig source) :
    (term.substitute source (.mapping AST.var)).alphaEquiv term = true := by
  apply alphaEquiv_of_lexical_eq
  rw [interpret_substitute]
  exact interpret_identity term _ (fun _ => rfl)

/-- Refreshing bound names preserves α-equivalence, including in open terms. -/
theorem refresh_alphaEquiv (term : AST sig source) :
    (term.refresh source).alphaEquiv term = true := by
  apply alphaEquiv_of_lexical_eq
  rw [refresh, interpret_substituteRefreshed]
  exact interpret_identity term _ (fun _ => rfl)

/-- Applying substitutions sequentially agrees with their composition up to α-equivalence. -/
theorem substitute_compose (term : AST sig source) (first : Substitution sig source middle)
    (second : Substitution sig middle target) :
    ((term.substitute middle first).substitute target second).alphaEquiv
      (term.substitute target (first.compose second)) = true := by
  apply alphaEquiv_of_lexical_eq
  rw [interpret_substitute, interpret_substitute, interpret_substitute]
  exact interpret_compose term first second _ _

/-- Composition also holds when both traversals explicitly refresh every binder. -/
theorem substituteRefreshed_compose (term : AST sig source)
    (first : Substitution sig source middle) (second : Substitution sig middle target) :
    ((term.substituteRefreshed middle first).substituteRefreshed target second).alphaEquiv
      (term.substitute target (first.compose second)) = true := by
  apply alphaEquiv_of_lexical_eq
  rw [interpret_substituteRefreshed, interpret_substituteRefreshed, interpret_substitute]
  exact interpret_compose term first second _ _

end FreeFoil.AST

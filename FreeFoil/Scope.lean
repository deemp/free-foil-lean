import Std

namespace FreeFoil

/-- A lexical context, with the most recent names first. A sunk term may shadow ambient names. -/
abbrev Scope := List Nat

/-- A numeric name together with evidence that it is in scope. -/
def Name (scope : Scope) := { id : Nat // id ∈ scope }

namespace Name

instance (scope : Scope) : DecidableEq (Name scope) := inferInstanceAs (DecidableEq (Subtype _))

abbrev id (name : Name scope) : Nat := name.val

def ofId (scope : Scope) (id : Nat) : Option (Name scope) :=
  if h : id ∈ scope then some ⟨id, h⟩ else none

/-- Widen the context of a name without changing its identifier. -/
def sink (h : source ⊆ target) (name : Name source) : Name target :=
  ⟨name.id, h name.property⟩

end Name

namespace Scope

/-- The first number above the maximum identifier, starting at zero in an empty scope. -/
def nextId : Scope → Nat
  | [] => 0
  | id :: rest => max (id + 1) (nextId rest)

theorem lt_nextId {id : Nat} {scope : Scope} (mem : id ∈ scope) : id < nextId scope := by
  induction scope with
  | nil => simp at mem
  | cons first rest ih =>
    rcases List.mem_cons.mp mem with eq | tail
    · subst id
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left ..)
    · exact Nat.lt_of_lt_of_le (ih tail) (Nat.le_max_right ..)

theorem nextId_not_mem (scope : Scope) : nextId scope ∉ scope :=
  fun mem => Nat.lt_irrefl _ (lt_nextId mem)

/-- Allocate a name and extend the context with it. -/
def fresh (scope : Scope) : Name (nextId scope :: scope) := ⟨nextId scope, by simp⟩

end Scope
end FreeFoil

import FreeFoil.Examples.NbEDemos.Functions
import FreeFoil.Examples.NbEDemos.Monolith
import FreeFoil.Examples.NbEDemos.Pairs
import FreeFoil.Examples.NbEDemos.Naturals

namespace FreeFoil.Examples.NbEDemos.Fragments

open Monolith (Pattern)

abbrev sig := Functions.sig.sum (Pairs.sig.sum Naturals.sig Pattern Pattern.binders)
  Pattern Pattern.binders

def fragment : NbE.Fragment sig := Functions.fragment.sum (Pairs.fragment.sum Naturals.fragment)

def nbeRules : NbE.Rules sig NbE.NoContext := fragment.rules

private def fromOp : Monolith.Op → sig.Op
  | .lam => .inl .lam
  | .app => .inl .app
  | .pi => .inl .pi
  | .pair => .inr (.inl .pair)
  | .first => .inr (.inl .first)
  | .second => .inr (.inl .second)
  | .split => .inr (.inl .split)
  | .zero => .inr (.inr .zero)
  | .suc => .inr (.inr .suc)
  | .natrec => .inr (.inr .natrec)

private def toOp : sig.Op → Monolith.Op
  | .inl .lam => .lam
  | .inl .app => .app
  | .inl .pi => .pi
  | .inr (.inl .pair) => .pair
  | .inr (.inl .first) => .first
  | .inr (.inl .second) => .second
  | .inr (.inl .split) => .split
  | .inr (.inr .zero) => .zero
  | .inr (.inr .suc) => .suc
  | .inr (.inr .natrec) => .natrec

private def fromPosition : Monolith.sig.Embedding sig where
  op := fromOp
  terms op := by cases op <;> rfl
  scopes op := by cases op <;> rfl

private def toPosition : sig.Embedding Monolith.sig where
  op := toOp
  terms op := by rcases op with op | op | op <;> cases op <;> rfl
  scopes op := by rcases op with op | op | op <;> cases op <;> rfl

def fromMonolith (term : Monolith.Term scope) : AST sig scope :=
  fromPosition.mapAST (fun shape => ⟨shape, rfl⟩) term

def toMonolith (term : AST sig scope) : Monolith.Term scope :=
  toPosition.mapAST (fun shape => ⟨shape, rfl⟩) term

def parse (source : String) : Except String (Syntax sig String) :=
  (Monolith.parse source).map (fromPosition.mapSyntax fun shape => ⟨shape, rfl⟩)

def pretty (term : Syntax sig String) : String :=
  Monolith.pretty (toPosition.mapSyntax (fun shape => ⟨shape, rfl⟩) term)

end FreeFoil.Examples.NbEDemos.Fragments

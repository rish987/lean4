import Lean.Meta.Tactic.DfEq

axiom S : (A : Type) → (B : A → Type) → Type
axiom mkS : (A : Type) → (B : A → Type) → (a : A) → B a → S A B


-- @[dfeq]
-- axiom add_1 (n : Nat) : 1 + n = .succ n
--
-- theorem test (n : Nat) : 1 + n = .succ n := Eq.refl (1 + n)

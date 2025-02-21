import Lean.Meta.Tactic.DfEq

structure S where
x : Nat
y : Nat
z : Nat

def S.structEtaAux (s : S) : s = S.mk s.x s.y s.z :=
  @s.rec (fun s' => s' = S.mk s'.x s'.y s'.z) (fun x y z => Eq.refl (S.mk x y z))

def S.structEta (s s' : S) (hx : s.x = s'.x) (hy : s.y = s'.y) (hz : s.z = s'.z) : s = S.mk s'.x s'.y s'.z := sorry

-- @[dfeq]
-- axiom add_1 (n : Nat) : 1 + n = .succ n
--
-- theorem test (n : Nat) : 1 + n = .succ n := Eq.refl (1 + n)

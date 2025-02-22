import Lean.Meta.Tactic.DfEq

structure S (T : Type) (F : T → Type) where
x : T
y : F x
z : T

def S.structEta (T : Type) (F : T → Type) (s : S T F) : s = S.mk s.x s.y s.z :=
  @s.rec T F (fun s' => s' = S.mk s'.x s'.y s'.z) (fun x y z => Eq.refl (S.mk x y z))

-- #print S.mk
-- def S.structEta (T : Type) (F : T → Type) (s s' : S T F) (hx : s.x = s'.x) (hy : s.y = s'.y) (hz : s.z = s'.z) : s = S.mk s'.x s'.y s'.z := sorry

def f : Bool → Type
| .true => Unit
| .false => Bool

inductive K : (b : Bool) → Bool → (x : f b) → Type where
| mk b x : K b b x

inductive MEq : α → α → Prop where
  /-- `Eq.refl a : a = a` is reflexivity, the unique constructor of the
  equality type. See also `rfl`, which is usually used instead. -/
  | refl (a : α) : MEq a a

#print MEq.rec
#print K.rec

theorem K.k (b : Bool) (x : f b) (k : K b b x) : k = K.mk b x := by
  cases k
  rfl
#print K.k
  -- @k.rec b (fun b' x' k' => k' = K.mk b' x') (Eq.refl (@K.mk T b x))

-- @[dfeq]
-- axiom add_1 (n : Nat) : 1 + n = .succ n

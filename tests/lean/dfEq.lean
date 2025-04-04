-- structure S (T : Type) (F : T → Type) where
-- x : T
-- y : F x
-- z : T
--
-- def S.structEta (T : Type) (F : T → Type) (s : S T F) : s = S.mk s.x s.y s.z :=
--   @s.rec T F (fun s' => s' = S.mk s'.x s'.y s'.z) (fun x y z => Eq.refl (S.mk x y z))
--
-- -- #print S.mk
-- -- def S.structEta (T : Type) (F : T → Type) (s s' : S T F) (hx : s.x = s'.x) (hy : s.y = s'.y) (hz : s.z = s'.z) : s = S.mk s'.x s'.y s'.z := sorry
--
-- def f : Bool → Type
-- | .true => Unit
-- | .false => Bool
--
-- inductive K : (b : Bool) → Bool → (x : f b) → Type where
-- | mk b x : K b b x
--
-- inductive MEq : α → α → Prop where
--   /-- `Eq.refl a : a = a` is reflexivity, the unique constructor of the
--   equality type. See also `rfl`, which is usually used instead. -/
--   | refl (a : α) : MEq a a
--
-- #print MEq.rec
-- #print K.rec
--
-- theorem K.k (b : Bool) (x : f b) (k : K b b x) : k = K.mk b x := by
--   cases k
--   rfl
-- #print K.k
--
inductive Vec : Nat → Type where
| nil : Vec 0
| cons {n : Nat} (v : Vec n) (x : Nat) : Vec (Nat.succ n)

-- @[drw]
-- theorem succAddComm (x : Nat) : (.succ x) + n = Nat.succ (x + n) := sorry
@[drw]
theorem succAddComm (x : Nat) : Nat.add (.succ x) n = Nat.succ (Nat.add x n) := sorry

@[drw]
theorem zeroAddComm : Nat.add Nat.zero n = n := sorry

-- @[rw] -- bad rule leading to non-termination
-- theorem succComm : Nat.succ n = 1 + n := sorry

def s := Nat.succ
def z := Nat.zero

def add := fun x y => Nat.add x y

-- set_option trace.Kernel.ext true in
example : Nat.add z n = n := @Eq.refl _ n
-- set_option trace.Kernel.ext true in
-- example : add (add z (s z)) n = s n := @Eq.refl _ (Nat.add Nat.zero n)
def vecTest (n : Nat) (v : Vec n) : Vec (Nat.add (.succ .zero) n) :=
v.cons 1

-- set_option pp.all true in
-- #print vecTest

-- set_option trace.Meta.isDefEq true in
-- example : Nat := 1
-- example (x y : Nat) : y + (1 + x) = Nat.succ (y + x) := by rfl
example (x y : Nat) : Nat.add y (.add (.succ .zero) x) = Nat.succ (.add y x) := by rfl
-- example (x y : Nat) : Nat.add (.add (.succ .zero) y) x = Nat.succ (.add y x) := by rfl
-- example (xy : Nat) : Nat.add (Nat.add 1 y) x = Nat.succ (Nat.add y x) := rfl -- does not work, need some way to mark the first argument for eager expansion

-- (1 + y) + x --> succ (zero + y) + x
-- 1 + y --> succ (zero + y)

-- @[deq]
-- theorem h (x y z : Nat) (hy : y = 0) (hz : z = x) : x + y = z := sorry

-- theorem ex (a b c : Nat) (ha : b ≡ 0) (hc : c ≡ a) : a + b = c := rfl

-- @[deq]
-- theorem h (x y z : Nat) (hy : y = 0) (hz : z = x) : x + y = z := sorry

-- theorem ex3 (h : ldeq ((x y z : Nat) → (hy : y = 0) → (hz : z = x) → x + y = z)) (a b c : Nat) (ha : b ≡ 0) (hc : c ≡ a) : a + b = c := Eq.refl (c)

-- example (a b c : Nat) (ha : b = 0) (hc : c = a) : a + b = c := ex a b c ha hc
-- theorem thm (x y z : Nat) (hy : y = 0) (hz : z = x) : x + y = z := sorry

-- set_option pp.explicit true in
-- #print localDfEqEx
-- theorem localDfEqEx : (a b c : Nat) → (h : localDfEq (a + b = c)) → a + b = c :=
--   fun (a b c : Nat) (h : localDfEq (a + b = c)) => @Eq.refl Nat (a + b)

  -- @k.rec b (fun b' x' k' => k' = K.mk b' x') (Eq.refl (@K.mk T b x))

-- @[dfeq]
-- axiom add_1 (n : Nat) : 1 + n = .succ n

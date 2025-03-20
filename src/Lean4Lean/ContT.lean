def ContT (r : Type) (m : Type → Type u) (α : Type) :=
  (α → m r) → m r

namespace ContT

variable {r : Type} {m : Type → Type v} {α β : Type}

def run : ContT r m α → (α → m r) → m r :=
  id

def run' [Monad m] (c : ContT r m r) : m r := do
  c.run fun x => do pure x

-- TODO why doesn't this work?
instance [Monad m] : Coe (ContT r m r) (m r) where
  coe m := m.run'

def map (f : m r → m r) (x : ContT r m α) : ContT r m α :=
  f ∘ x

theorem run_contT_map_contT (f : m r → m r) (x : ContT r m α) : run (map f x) = f ∘ run x :=
  rfl

def withContT (f : (β → m r) → α → m r) (x : ContT r m α) : ContT r m β := fun g => x <| f g

theorem run_withContT (f : (β → m r) → α → m r) (x : ContT r m α) :
    run (withContT f x) = run x ∘ f :=
  rfl

@[ext]
protected theorem ext {x y : ContT r m α} (h : ∀ f, x.run f = y.run f) : x = y := by
  unfold ContT; ext; apply h

instance : Monad (ContT r m) where
  pure x f := f x
  bind x f g := x fun i => f i g

instance : LawfulMonad (ContT r m) := LawfulMonad.mk'
  (id_map := by intros; rfl)
  (pure_bind := by intros; ext; rfl)
  (bind_assoc := by intros; ext; rfl)

def monadLift [Monad m] {α} : m α → ContT r m α := fun x f => x >>= f

instance [Monad m] : MonadLift m (ContT r m) where
  monadLift := ContT.monadLift

theorem monadLift_bind [Monad m] [LawfulMonad m] {α β} (x : m α) (f : α → m β) :
    (monadLift (x >>= f) : ContT r m β) = monadLift x >>= monadLift ∘ f := by
  ext
  simp only [monadLift, MonadLift.monadLift, (· ∘ ·), (· >>= ·), bind_assoc, id, run,
    ContT.monadLift]

instance (ε) [MonadExcept ε m] : MonadExcept ε (ContT r m) where
  throw e _ := throw e
  tryCatch act h f := tryCatch (act f) fun e => h e f

def dud [Monad m] (c : ContT r m r) : ContT T m r := do
  liftM $ ContT.run' c

-- instance [Monad m] [Monad m] : MonadControl m (ContT T m) where
--   stM      := fun x => T
--   liftWith f := do monadLift (f (fun x => liftM x))
--   restoreM x _ := x
--

instance [Monad m] (ε) [MonadExceptOf ε m] : MonadExceptOf ε (ContT ρ m) where
  throw e  := liftM (m := m) (throw e)
  tryCatch := fun x c r => tryCatchThe ε (x r) (fun e => (c e) r)

instance (ρ m) : MonadFunctor m (ContT ρ m) where
  monadMap f x := fun ctx => f (x ctx)

end ContT

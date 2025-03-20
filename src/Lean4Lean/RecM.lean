import Lean4Lean.Declaration
import Lean4Lean.Level
import Lean4Lean.Quot
import Lean4Lean.Inductive.Reduce
import Lean4Lean.Instantiate
import Lean4Lean.ForEachExprV
import Lean4Lean.EquivManager
import Lean4Lean.ContT
import Lean.Meta.Tactic.DfEq
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Replace
import Lean.Meta.Tactic.Refl

namespace Lean

abbrev InferCache := ExprMap Expr

structure TypeChecker.State where
  ngen : NameGenerator := { namePrefix := `_kernel_fresh, idx := 0 }
  inferTypeI : InferCache := {}
  inferTypeC : InferCache := {}
  whnfCoreCache : ExprMap Expr := {}
  whnfCache : ExprMap Expr := {}
  eqvManager : EquivManager := {}
  failure : Std.HashSet (Expr × Expr) := {}

structure TypeChecker.Context where
  env : Kernel.Environment
  env' : Environment
  lctx : LocalContext := {}
  options : Options := default
  fuel : Nat := 5
  safety : DefinitionSafety := .safe
  lparams : List Name := []

namespace TypeChecker

instance (ω σ : Type) : MonadControl MetaM (StateT ω MetaM) :=
  inferInstance

instance (ω σ : Type) : MonadControl MetaM (StateT ω MetaM) :=
  inferInstance

abbrev M := ReaderT Context <| StateT State <| MetaM

instance : MonadControlT MetaM (M) :=
  inferInstance

abbrev MO (T : Type) := ContT T M

def M.run (env : Kernel.Environment) (env' : Environment) (safety : DefinitionSafety := .safe) (lctx : LocalContext := {}) (options : Options)
    (x : M α) (fuel := 5) (localDfEqs : List Expr := []) : MetaM α :=
  x { env, env', safety, lctx, fuel, options } |>.run' {}

-- instance : MonadEnv M where
--   getEnv := return (← read).env
--   modifyEnv _ := pure ()

def getKEnv : M Kernel.Environment := return (← read).env

instance : MonadLCtx M where
  getLCtx := return (← read).lctx

instance [Monad m] : MonadNameGenerator (StateT State m) where
  getNGen := return (← get).ngen
  setNGen ngen := modify fun s => { s with ngen }

instance (priority := low) : MonadWithReaderOf LocalContext M where
  withReader f := withReader fun s => { s with lctx := f s.lctx }

structure Methods where
  isDefEqCore : Nat → Expr → Expr → Level → Expr → MO T Bool
  whnfCore (e : Expr) (l : Option (Level × Expr) := none) (cheapRec := false) (cheapProj := false) : MO T Expr
  whnf (e : Expr) (d : Option (Level × Expr)) : MO T Expr 
  inferType (e : Expr) (inferOnly : Bool) : MO T Expr

abbrev RecM := ReaderT Methods M
abbrev RecMO (T : Type) := ContT T RecM
abbrev RecMB := ContT Bool RecM

-- TODO can this be derived from a more general rule?
instance (priority := low) : MonadWithReaderOf LocalContext RecM where
  withReader f m := fun b c => m b ({c with lctx := f c.lctx})

-- TODO can this be derived from a more general rule?
instance (priority := low) : MonadWithReaderOf LocalContext (RecMO T) where
  withReader f m := fun b meths c => m b meths ({c with lctx := f c.lctx})

inductive ReductionStatus where
  | continue (tn sn : Expr)
  | unknown (tn sn : Expr)
  | bool (b : Bool)

namespace Inner

def isDefEqCore (n : Nat) (t s : Expr) (l : Level) (T : Expr) : RecMO U Bool := fun f m => m.isDefEqCore n t s l T (fun a => f a m)

def whnfCore (e : Expr) (l : Option (Level × Expr) := none) (cheapRec := false) (cheapProj := false) : RecMO T Expr :=
  -- TODO what exactly is going on here?
  fun f m => m.whnfCore e l cheapRec cheapProj fun e => f e m


def whnf (e : Expr) (d : Option (Level × Expr) := none) : RecMO T Expr := fun f m => m.whnf e d fun e => f e m

def inferType (e : Expr) (inferOnly := true) : RecMO T Expr := fun f m => m.inferType e inferOnly fun a => f a m

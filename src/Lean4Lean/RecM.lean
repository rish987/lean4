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
import Lean.Meta.Tactic.Util

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
  mctx : MetavarContext := default
  -- traceState : TraceState := default

structure TypeChecker.Context where
  env : Kernel.Environment
  env' : Environment
  lctx : LocalContext := {}
  options : Options := default
  fuel : Nat := 5
  safety : DefinitionSafety := .safe
  lparams : List Name := []

namespace TypeChecker

-- instance (ω σ : Type) : MonadControl MetaM (StateT ω MetaM) :=
--   inferInstance
--
-- instance (ω σ : Type) : MonadControl MetaM (StateT ω MetaM) :=
--   inferInstance

abbrev M := ReaderT Context <| StateT State <| EIO KernelException

-- instance : MonadControlT MetaM (M) :=
--   inferInstance

abbrev MO (T : Type) := ContT T M

def M.run (env : Kernel.Environment) (env' : Environment) (safety : DefinitionSafety := .safe) (lctx : LocalContext := {}) (options : Options)
    (x : M α) (fuel := 5) (localDfEqs : List Expr := []) : EIO KernelException α :=
  x { env, env', safety, lctx, fuel, options } |>.run' {}

instance : MonadMCtx M where
  getMCtx    := return (← get).mctx
  modifyMCtx f := modify fun s => { s with mctx := f s.mctx }

instance : MonadOptions M where
  getOptions := do pure (← read).options

-- instance : MonadTrace M where
--   modifyTraceState f := do modify fun s => {s with traceState := f s.traceState}
--   getTraceState := do pure (← get).traceState

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
  whnfCoreNoExt (e : Expr) (l : Option (Level × Expr) := none) (cheapRec := false) (cheapProj := false) : MO T Expr
  whnf (e : Expr) (d : Option (Level × Expr)) : MO T Expr 
  inferType (e : Expr) (inferOnly : Bool) : MO T Expr

abbrev RecM := ReaderT Methods M
abbrev RecMO (T : Type) := ContT T RecM
abbrev RecMB := ContT Bool RecM

def isDelta (env : Kernel.Environment) (e : Expr) : Option ConstantInfo := do
  if let .const c _ := e.getAppFn then
    if let some ci := env.find? c then
      if ci.hasValue then
        return ci
  none

def unfoldDefinitionCore (env : Kernel.Environment) (e : Expr) : Option Expr := do
  if let .const _ ls := e then
    if let some d := isDelta env e then
      if ls.length == d.numLevelParams then
        return d.instantiateValueLevelParams! ls
  none

def unfoldDefinition (env : Kernel.Environment) (e : Expr) : Option Expr := do
  if e.isApp then
    let f0 := e.getAppFn
    if let some f := unfoldDefinitionCore env f0 then
      let rargs := e.getAppRevArgs
      return f.mkAppRevRange 0 rargs.size rargs
    none
  else
    unfoldDefinitionCore env e

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

def whnfCoreNoExt (e : Expr) (l : Option (Level × Expr) := none) (cheapRec := false) (cheapProj := false) : RecMO T Expr :=
  fun f m => m.whnfCoreNoExt e l cheapRec cheapProj fun e => f e m


def whnf (e : Expr) (d : Option (Level × Expr) := none) : RecMO T Expr := fun f m => m.whnf e d fun e => f e m

def inferType (e : Expr) (inferOnly := true) : RecMO T Expr := fun f m => m.inferType e inferOnly fun a => f a m

@[inline] def withLCtx {α : Type u} [MonadWithReaderOf LocalContext m] (lctx : LocalContext) (x : m α) : m α :=
  withReader (fun _ => lctx) x

-- instance : MonadTrace (RecMO T) :=
--   inferInstance
--
-- instance : MonadMCtx (RecMO T) :=
--   inferInstance

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

inductive CallData where
|  isDefEqCore : Expr → Expr → CallData
|  whnfCore (e : Expr) (cheapRec : Bool) (cheapProj : Bool) : CallData
|  whnfCoreNoExt (e : Expr) (cheapRec : Bool) (cheapProj : Bool) : CallData
|  whnf (e : Expr) : CallData
|  inferType (e : Expr) (inferOnly : Bool) : CallData
deriving Inhabited

instance : ToString CallData where
toString
| .isDefEqCore t s => s!"isDefEqCore ({t}) ({s})"
| .whnfCore e k p      => s!"whnfCore ({e}) {k} {p}"
| .whnfCoreNoExt e k p => s!"whnfCore ({e}) {k} {p}"
| .whnf e => s!"whnf ({e})"
| .inferType e d         => s!"inferType ({e}) ({d})"

def CallData.name : CallData → String
| .isDefEqCore ..     => "isDefEqCore"
| .whnfCore ..        => "whnfCore"
| .whnfCoreNoExt ..   => "whnfCore"
| .whnf ..            => "whnf"
| .inferType ..       => "inferType"

@[reducible]
def CallDataT : CallData → Type
| .isDefEqCore ..     => Bool
| .whnfCore ..        => Expr
| .whnfCoreNoExt ..   => Expr
| .whnf ..            => Expr
| .inferType ..       => Expr

structure TypeChecker.State where
  ngen : NameGenerator := { namePrefix := `_kernel_fresh, idx := 0 }
  inferTypeI : InferCache := {}
  inferTypeC : InferCache := {}
  whnfCoreCache : ExprMap Expr := {}
  whnfCache : ExprMap Expr := {}
  eqvManager : EquivManager := {}
  failure : Std.HashSet (Expr × Expr) := {}
  mctx : MetavarContext := default
  numCalls : Nat := 0
  -- traceState : TraceState := default

structure TypeChecker.Context where
  env : Kernel.Environment
  env' : Environment
  lctx : LocalContext := {}
  options : Options := default
  fuel : Nat := 5
  safety : DefinitionSafety := .safe
  lparams : List Name := []
  callStack : Array (Nat × Nat × CallData) := #[]
  callId : Nat := 0

namespace TypeChecker

@[inline] def withCallData [MonadWithReaderOf Context m] (i : Nat) (id : Nat) (d : CallData) (x : m α) : m α :=
  withReader (fun c => {c with callStack := c.callStack.push (i, id, d)}) x

@[inline] def withCallId [MonadWithReaderOf Context m] (id : Nat) (x : m α) : m α :=
  withReader (fun c => {c with callId := id}) x

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
  isDefEqCore : Nat → Expr → Expr → MO T Bool
  whnfCore (n : Nat) (e : Expr) (cheapRec := false) (cheapProj := false) : MO T Expr
  whnfCoreNoExt (n : Nat) (e : Expr) (cheapRec := false) (cheapProj := false) : MO T Expr
  whnf (n : Nat) (e : Expr) : MO T Expr 
  inferType (n : Nat) (e : Expr) (inferOnly : Bool) : MO T Expr

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

def isDefEqCore (n : Nat) (t s : Expr) : RecMO U Bool := fun f m => m.isDefEqCore n t s (fun a => f a m)

def whnfCore (n : Nat) (e : Expr) (cheapRec := false) (cheapProj := false) : RecMO T Expr :=
  -- TODO what exactly is going on here?
  fun f m => m.whnfCore n e cheapRec cheapProj fun e => f e m

def whnfCoreNoExt (n : Nat) (e : Expr) (cheapRec := false) (cheapProj := false) : RecMO T Expr :=

  fun f m => m.whnfCoreNoExt n e cheapRec cheapProj fun e => f e m


def whnf (n : Nat) (e : Expr) : RecMO T Expr := fun f m => m.whnf n e fun e => f e m

def inferType (n : Nat) (e : Expr) (inferOnly := true) : RecMO T Expr := fun f m => m.inferType n e inferOnly fun a => f a m

@[inline] def withLCtx {α : Type u} [MonadWithReaderOf LocalContext m] (lctx : LocalContext) (x : m α) : m α :=
  withReader (fun _ => lctx) x

def ensureSortCore (e : Expr) (s : Expr) : RecMO T Expr := ContT.dud do
  if e.isSort then return e
  let e ← whnf 27 e
  if e.isSort then return e
  throw <| .typeExpected (← getKEnv) (← getLCtx) s

def getTypeInfo (n : Nat) (t : Expr) : RecMO T (Level × Expr) := do
  let tT ← inferType (43000 + n) t
  let tTT ← inferType (44000 + n) tT
  -- note that it is important that we do not immediately run `whnf tTT`,
  -- as this would cause non-termination: we call this function in `whnf`
  -- itself to get the information needed for β rules
  let .sort l ← ensureSortCore tTT tT | unreachable!
  pure (l, tT)

-- instance : MonadTrace (RecMO T) :=
--   inferInstance
--
-- instance : MonadMCtx (RecMO T) :=
--   inferInstance

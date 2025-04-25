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
|  whnfCore (e : Expr) (cheapRec : Bool) (cheapProj : Bool) (skipLem? : Option (Name ⊕ FVarId) := none) : CallData
|  whnfCoreNoExt (e : Expr) (cheapRec : Bool) (cheapProj : Bool) : CallData
|  whnf (e : Expr) (ext : Bool) : CallData
|  inferType (e : Expr) (inferOnly : Bool) : CallData
|  extMatch (typ : Expr )(getT : (List (List Expr → Expr))) (localMarker : Name) (lems : List Name) (dbg := false) (skipLem? : Option (Name ⊕ FVarId)) : CallData
deriving Inhabited

instance : ToString CallData where
toString
| .isDefEqCore t s     => s!"isDefEqCore ({t}) ({s})"
| .whnfCore e k p _    => s!"whnfCore ({e}) {k} {p} "
| .whnfCoreNoExt e k p => s!"whnfCore ({e}) {k} {p}"
| .whnf e ext          => s!"whnf ({e}, {ext})"
| .inferType e d       => s!"inferType ({e}) ({d})"
| .extMatch T getT ..    => Id.run $ do
    let mut es := #[]
    let mut subs := []
    for i in [:getT.length] do
      es := es.push (getT[i]! subs)
      subs := subs ++ [Expr.bvar i]
    pure s!"extMatch ({T}): {es}"

def CallData.name : CallData → String
| .isDefEqCore ..     => "isDefEqCore"
| .whnfCore ..        => "whnfCore"
| .whnfCoreNoExt ..   => "whnfCore"
| .whnf ..            => "whnf"
| .inferType ..       => "inferType"
| .extMatch ..        => "extMatch"

@[reducible]
def CallDataT : CallData → Type
| .isDefEqCore ..     => Bool
| .whnfCore ..        => Expr
| .whnfCoreNoExt ..   => Expr
| .whnf ..            => Expr
| .inferType ..       => Expr
| .extMatch ..        => Option (Expr × List Expr) 

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

structure IsDefEqOpts where
  ext : Bool := false
deriving Inhabited

structure TypeChecker.Context where
  env : Kernel.Environment
  env' : Environment
  lctx : LocalContext := {}
  extLemsReducing : List (Name ⊕ FVarId) := default
  options : Options := default
  dfEqOpts : IsDefEqOpts := default
  fuel : Nat := 5
  safety : DefinitionSafety := .safe
  lparams : List Name := []
  callStack : Array (Nat × Nat × CallData) := #[]
  callId : Nat := 0

namespace TypeChecker

@[inline] def withCallData [MonadWithReaderOf Context m] (i : Nat) (id : Nat) (d : CallData) (x : m α) : m α :=
  withReader (fun c => {c with callStack := c.callStack.push (i, id, d)}) x

@[inline] def withDfEqOpts [MonadWithReaderOf Context m] (o : IsDefEqOpts) (x : m α) : m α :=
  withReader (fun c => {c with dfEqOpts := o}) x

@[inline] def withCallId [MonadWithReaderOf Context m] (id : Nat) (x : m α) : m α :=
  withReader (fun c => {c with callId := id}) x

@[inline] def withExtLemReducing [MonadWithReaderOf Context m] (lemName : Name ⊕ FVarId) (x : m α) : m α :=
  withReader (fun c => {c with extLemsReducing := c.extLemsReducing.insert lemName}) x

-- instance (ω σ : Type) : MonadControl MetaM (StateT ω MetaM) :=
--   inferInstance
--
-- instance (ω σ : Type) : MonadControl MetaM (StateT ω MetaM) :=
--   inferInstance

abbrev M := ReaderT Context <| StateT State <| EIO KernelException

-- instance : MonadControlT MetaM (M) :=
--   inferInstance

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
  isDefEqCore : Nat → Expr → Expr → M Bool
  whnfCore (n : Nat) (e : Expr) (cheapRec := false) (cheapProj := false) (skipLem? : Option (Name ⊕ FVarId)) : M Expr
  whnfCoreNoExt (n : Nat) (e : Expr) (cheapRec := false) (cheapProj := false) : M Expr
  whnf (n : Nat) (e : Expr) (ext : Bool := true) : M Expr 
  inferType (n : Nat) (e : Expr) (inferOnly : Bool) : M Expr
  extMatch (n : Nat) (typ : Expr) (getT : (List (List Expr → Expr))) (localMarker : Name) (lems : List Name) (dbg := false) (skipLem? : Option (Name ⊕ FVarId)) : M (Option (Expr × List Expr))

abbrev RecM := ReaderT Methods M

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
instance (priority := low) : MonadWithReaderOf LocalContext RecM where
  withReader f m := fun meths c => m meths ({c with lctx := f c.lctx})

inductive ReductionStatus where
  | continue (tn sn : Expr)
  | unknown (tn sn : Expr)
  | bool (b : Bool)

namespace Inner

def isDefEqCore (n : Nat) (t s : Expr) : RecM Bool := fun m => m.isDefEqCore n t s

def whnfCore (n : Nat) (e : Expr) (cheapRec := false) (cheapProj := false) (skipLem? : Option (Name ⊕ FVarId) := none) : RecM Expr :=
  -- TODO what exactly is going on here?
  fun m => m.whnfCore n e cheapRec cheapProj skipLem?

def whnfCoreNoExt (n : Nat) (e : Expr) (cheapRec := false) (cheapProj := false) : RecM Expr :=
  fun m => m.whnfCoreNoExt n e cheapRec cheapProj

def extMatch (n : Nat) (typ : Expr) (getT : (List (List Expr → Expr))) (localMarker : Name) (lems : List Name) (dbg := false) (skipLem? : Option (Name ⊕ FVarId)) : RecM (Option (Expr × List Expr)) :=
  fun m => m.extMatch n typ getT localMarker lems dbg skipLem?

def whnf (n : Nat) (e : Expr) (ext : Bool := true) : RecM Expr := fun m => m.whnf n e ext

def inferType (n : Nat) (e : Expr) (inferOnly := true) : RecM Expr := fun m => m.inferType n e inferOnly

def ensureSortCore (e : Expr) (s : Expr) : RecM Expr := do
  if e.isSort then return e
  let e ← whnf 27 e
  if e.isSort then return e
  throw <| .typeExpected (← getKEnv) (← getLCtx) s

def getTypeInfo (n : Nat) (t : Expr) : RecM (Level × Expr) := do
  let tT ← inferType (43000 + n) t
  let tTT ← inferType (44000 + n) tT
  -- note that it is important that we do not immediately run `whnf tTT`,
  -- as this would cause non-termination: we call this function in `whnf`
  -- itself to get the information needed for β rules
  let .sort l ← ensureSortCore tTT tT | unreachable!
  pure (l, tT)

def reduceExt (n : Nat) (e : Expr) (dbg : Bool := false) (skipLem? : Option (Name ⊕ FVarId)) : RecM (Option Expr) := do
  let (l, T) ← getTypeInfo 2 e
  let mut dbg := dbg
  -- if let (.app (.app (.const `Nat.add []) (.lit (.natVal 0))) n) := e then
  -- if let (.app (.app (.const `Nat.add []) x) n) := e then
  --   if let .const `Nat.zero _  := x.getAppFn then
  --     dbg := true
  let getVars := [fun _ => T, fun ms => mkAppN (.const `Eq [l]) #[T, e, ms[0]!]]
  if let some (_, ts) ← extMatch (100 + n) T getVars ``ldrw (Lean.Meta.DfEq.rwExt.getState (← readThe Context).env') dbg skipLem? then 
    return .some ts[0]!
  return none

def mkFreshId'.{u} {m : Type → Type u} [Monad m] [MonadNameGenerator m] (n : Nat) : m FVarId := do
  let id := ← mkFreshId
  -- if id == "_kernel_fresh.2769".toName then
  --   dbg_trace s!"DBG[412]: RecM.lean:240 {n}"
  pure ⟨id⟩

-- instance : MonadTrace (RecMO T) :=
--   inferInstance
--
-- instance : MonadMCtx (RecMO T) :=
--   inferInstance

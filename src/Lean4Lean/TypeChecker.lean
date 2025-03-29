import Lean4Lean.Declaration
import Lean4Lean.Level
import Lean4Lean.Quot
import Lean4Lean.Inductive.Reduce
import Lean4Lean.Instantiate
import Lean4Lean.ForEachExprV
import Lean4Lean.EquivManager
import Lean4Lean.ContT
import Lean4Lean.Ext
import Lean.Meta.Tactic.DfEq
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Replace
import Lean.Meta.Tactic.Refl

namespace Lean.TypeChecker.Inner

-- def noProp

def ensureSortCore (e : Expr) (s : Expr) (d : Option (Level × Expr) := none) : RecMO T Expr := ContT.dud do
  if e.isSort then return e
  let e ← whnf e d
  if e.isSort then return e
  throw <| .typeExpected (← getKEnv) (← getLCtx) s

def ensureForallCore (e : Expr) (s : Expr) (d : Option (Level × Expr) := none) : RecMO T Expr := ContT.dud do
  if e.isForall then return e
  let e ← whnf e d
  if e.isForall then return e
  throw <| .funExpected (← getKEnv) (← getLCtx) s

def checkLevel (tc : Context) (l : Level) : EIO KernelException Unit := do
  if let some n2 := l.getUndefParam tc.lparams then
    throw <| .other s!"invalid reference to undefined universe level parameter '{n2}'"

def inferFVar (tc : Context) (name : FVarId) : EIO KernelException Expr := do
  if let some decl := tc.lctx.find? name then
    return decl.type
  throw <| .other "unknown free variable"

def inferMVar (tc : State) (name : MVarId) : EIO KernelException Expr := do
  if let some decl := tc.mctx.findDecl? name then
    return decl.type
  throw <| .other "unknown meta variable"

def inferConstant (tc : Context) (name : Name) (ls : List Level) (inferOnly : Bool) :
    EIO KernelException Expr := do
  let e := Expr.const name ls
  let info ← tc.env.get name
  let ps := info.levelParams
  if ps.length != ls.length then
    throw <| .other s!"incorrect number of universe levels parameters for '{e
      }', #{ps.length} expected, #{ls.length} provided"
  if !inferOnly then
    if info.isUnsafe && tc.safety != .unsafe then
      throw <| .other s!"invalid declaration, it uses unsafe declaration '{e}'"
    if let .defnInfo v := info then
      if v.safety == .partial && tc.safety == .safe then
        throw <| .other
          s!"invalid declaration, safe declaration must not contain partial declaration '{e}'"
    for l in ls do
      checkLevel tc l
  return info.instantiateTypeLevelParams ls

def inferLambda (e : Expr) (inferOnly : Bool) : RecMO T Expr := loop #[] e where
  loop fvars : Expr → RecMO T Expr
  | .lam name dom body bi => do
    let d := dom.instantiateRev fvars
    let id := ⟨← mkFreshId⟩
    withLCtx ((← getLCtx).mkLocalDecl id name d bi) do
      let fvars := fvars.push (.fvar id)
      if !inferOnly then
        let dType ← inferType d inferOnly
        _ ← ensureSortCore dType d none
      loop fvars body
  | e => do
    let r ← inferType (e.instantiateRev fvars) inferOnly
    let r := r.cheapBetaReduce
    return (← getLCtx).mkForall fvars r

def inferForall (e : Expr) (inferOnly : Bool) : RecMO T Expr := loop #[] #[] e where
  loop fvars us : Expr → RecMO T Expr
  | .forallE name dom body bi => do
    let d := dom.instantiateRev fvars
    let t1 ← ensureSortCore (← inferType d inferOnly) d
    let us := us.push t1.sortLevel!
    let id := ⟨← mkFreshId⟩
    withLCtx ((← getLCtx).mkLocalDecl id name d bi) do
      let fvars := fvars.push (.fvar id)
      loop fvars us body
  | e => do
    let r ← inferType (e.instantiateRev fvars) inferOnly
    let s ← ensureSortCore r e
    return .sort <| us.foldr mkLevelIMax' s.sortLevel!


def inferApp (e : Expr) : RecMO T Expr := do
  e.withApp fun f args => do
  let mut fType ← inferType f
  let mut j := 0
  for i in [:args.size] do
    match fType with
    | .forallE _ _ body _ =>
      fType := body
    | _ =>
      fType := fType.instantiateRevRange j i args
      let e ← ensureForallCore fType e none fun e => pure e
      fType := e.bindingBody!
      j := i
  return fType.instantiateRevRange j args.size args

def markUsed (n : Nat) (fvars : Array Expr) (b : Expr) (used : Array Bool) : Array Bool := Id.run do
  if !b.hasFVar then return used
  (·.2) <$> StateT.run (s := used) do
    b.forEachV' fun x => do
      if !x.hasFVar then return false
      if let .fvar name := x then
        for i in [:n] do
          if fvars[i]!.fvarId! == name then
            modify (·.set! i true)
            return false
      return true

def isDefEq (n : Nat) (t s : Expr) (l : Level) (T : Expr) : RecMO U Bool := do
  let r ← isDefEqCore n t s l T
  if r then
    modify fun st => { st with eqvManager := st.eqvManager.addEquiv t s }
  pure r

def inferLet (e : Expr) (inferOnly : Bool) : RecMO T Expr := loop #[] #[] e where
  loop fvars vals : Expr → RecMO T Expr
  | .letE name type val body _ => do
    let type := type.instantiateRev fvars
    let val := val.instantiateRev fvars
    let id := ⟨← mkFreshId⟩
    withLCtx ((← getLCtx).mkLetDecl id name type val) do
      let fvars := fvars.push (.fvar id)
      let vals := vals.push val
      if !inferOnly then
        let typeType ← inferType type inferOnly
        let .sort l ← ensureSortCore typeType type |>.run' | unreachable!
        let valType ← inferType val inferOnly
        if !(← isDefEq 1 valType type (.succ l) typeType) then
          throw <| .letTypeMismatch (← getKEnv) (← getLCtx) name valType type
      loop fvars vals body
  | e => do
    let r ← inferType (e.instantiateRev fvars) inferOnly
    let r := r.cheapBetaReduce
    let rec loopUsed i (used : Array Bool) :=
      match i with
      | 0 => used
      | i+1 =>
        let used := if used[i]! then markUsed i fvars vals[i]! used else used
        loopUsed i used
    let used := mkArray fvars.size false
    let used := markUsed fvars.size fvars r used
    let used := loopUsed fvars.size used
    let mut usedFVars := #[]
    for fvar in fvars, b in used do
      if b then
        usedFVars := usedFVars.push fvar
    return (← getLCtx).mkForall fvars r

def isProp (e : Expr) : RecMO T Bool :=
  return (← whnf (← inferType e) none) == .prop

def inferProj (typeName : Name) (idx : Nat) (struct structType : Expr) : RecMO T Expr := do
  let e := Expr.proj typeName idx struct
  let type ← whnf structType none
  type.withApp fun I args => do
  let env ← getKEnv
  let fail {_} := do throw <| .invalidProj env (← getLCtx) e
  let .const I_name I_levels := I | fail
  if typeName != I_name then fail
  let .inductInfo I_val ← env.get I_name | fail
  let [c] := I_val.ctors | fail
  if args.size != I_val.numParams + I_val.numIndices then fail
  let c_info ← env.get c
  let mut r := c_info.instantiateTypeLevelParams I_levels
  for i in [:I_val.numParams] do
    let .forallE _ _ b _ ← whnf r none | fail
    r := b.instantiate1 args[i]!
  let isPropType ← isProp type
  for i in [:idx] do
    let .forallE _ dom b _ ← whnf r none | fail
    if b.hasLooseBVars then
      if isPropType then if !(← isProp dom) then fail
      r := b.instantiate1 (.proj I_name i struct)
    else
      r := b
  let .forallE _ dom _ _ ← whnf r none | fail
  if isPropType then if !(← isProp dom) then fail
  return dom

def getTypeInfo (t : Expr) : RecMO T (Level × Expr) := do
  let tT ← inferType t
  let tTT ← inferType tT
  -- note that it is important that we do not immediately run `whnf tTT`,
  -- as this would cause non-termination: we call this function in `whnf`
  -- itself to get the information needed for β rules
  let .sort l ← ensureSortCore tTT tT | unreachable!
  pure (l, tT)

-- TODO an optimization to "tag" terms with their types during type inference
-- can avoid this, however we will need to use a custom `Expr` representation
def isDefEqCheckTypes (n : Nat) (t s : Expr) : RecMO T Bool := do
  let (l, tT) ← getTypeInfo t
  let sT ← inferType s
  unless ← isDefEq 2 tT sT (.succ l) (.sort l) do return false
  isDefEq n t s l tT

def inferType' (e : Expr) (inferOnly : Bool) : RecMO T Expr := do
  if e.isBVar then
    throw <| .other
      s!"type checker does not support loose bound variables, {""
        }replace them with free variables before invoking it"
  assert! !e.hasLooseBVars
  let state ← get
  if let some r := (cond inferOnly state.inferTypeI state.inferTypeC)[e]? then
    return r
  let r ← match e with
    | .lit l => pure l.type
    | .mdata _ e => inferType' e inferOnly
    | .proj s idx e => inferProj s idx e (← inferType' e inferOnly)
    | .fvar n => inferFVar (← readThe Context) n
    | .mvar n => inferMVar (← get) n
    | .bvar _ => unreachable!
    | .sort l =>
      if !inferOnly then
        checkLevel (← readThe Context) l
      pure <| .sort (.succ l)
    | .const c ls => inferConstant (← readThe Context) c ls inferOnly
    | .lam .. => inferLambda e inferOnly
    | .forallE .. => inferForall e inferOnly
    | .app f a =>
      if inferOnly then
        inferApp e
      else
        let fType ← ensureForallCore (← inferType' f inferOnly) e
        let aType ← inferType' a inferOnly
        let dType := fType.bindingDomain!
        if !(← isDefEqCheckTypes 15 dType aType) then
          -- dbg_trace s!"DBG[230]: TypeChecker.lean:286: fType=\n{fType}\n{aType}"
          throw <| .appTypeMismatch (← getKEnv) (← getLCtx) e fType aType
        pure <| fType.bindingBody!.instantiate1 a
    | .letE .. => inferLet e inferOnly
  modify fun s => cond inferOnly
    { s with inferTypeI := s.inferTypeI.insert e r }
    { s with inferTypeC := s.inferTypeC.insert e r }
  return r

def reduceRecursor (e : Expr) (l : Option (Level × Expr) := none) (cheapRec cheapProj : Bool) : RecMO T (Option Expr) := do
  let env ← getKEnv
  if env.quotInit then
    if let some r ← quotReduceRec e (whnf) then
      return r
  let whnf' e := if cheapRec then whnfCore e l cheapRec cheapProj else whnf e none
  if let some r ← inductiveReduceRec env e whnf' inferType (isDefEqCheckTypes 16) then
    return r
  return none

def whnfFVar (e : Expr) (l : Option (Level × Expr) := none) (cheapRec cheapProj : Bool) : RecMO T Expr := do
  if let some (.ldecl (value := v) ..) := (← getLCtx).find? e.fvarId! then
    return ← whnfCore v l cheapRec cheapProj
  return e

def reduceProj (idx : Nat) (struct : Expr) (cheapRec cheapProj : Bool) : RecMO T (Option Expr) := do
  let mut c ← (if cheapProj then whnfCore struct none cheapRec cheapProj else whnf struct)
  if let .lit (.strVal s) := c then
    c := .strLitToConstructor s
  c.withApp fun mk args => do
  let .const mkC _ := mk | return none
  let env ← getKEnv
  let .ctorInfo mkInfo ← env.get mkC | return none
  return args[mkInfo.numParams + idx]?

def isLetFVar (lctx : LocalContext) (fvar : FVarId) : Bool :=
  lctx.find? fvar matches some (.ldecl ..)

def whnfCoreNoExt' (e : Expr) (l : Option (Level × Expr) := none) (cheapRec := false) (cheapProj := false) : RecMO T Expr := do
  match e with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .const .. | .lam .. | .lit .. => return e
  | .mdata _ e => return ← whnfCoreNoExt' e l cheapRec cheapProj
  | .fvar id => if !isLetFVar (← getLCtx) id then return e
  | .app .. | .letE .. | .proj .. => pure ()
  if let some r := (← get).whnfCoreCache[e]? then
    return r
  let rec save r := do
    if !cheapRec && !cheapProj then
      modify fun s => { s with whnfCoreCache := s.whnfCoreCache.insert e r }
    return r
  match e with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .const .. | .lam .. | .lit ..
  | .mdata .. => unreachable!
  | .fvar _ => return ← whnfFVar e l cheapRec cheapProj
  | .app .. =>
    e.withAppRev fun f0 rargs => do
    let f ← whnfCore f0 none cheapRec cheapProj
    if let .lam _ _ body _ := f then
      let rec loop m (f : Expr) : RecMO T Expr :=
        let cont2 := do
          let r := f.instantiateRange (rargs.size - m) rargs.size rargs
          let r := r.mkAppRevRange 0 (rargs.size - m) rargs
          save <|← whnfCore r l cheapRec cheapProj
        if let .lam _ _ body _ := f then
          if m < rargs.size then loop (m + 1) body
          else cont2
        else cont2
      loop 1 body
    else if f == f0 then
      if let some r ← reduceRecursor e l cheapRec cheapProj then
        whnfCore r l cheapRec cheapProj
      else
        pure e
    else
      let r := f.mkAppRevRange 0 rargs.size rargs
      save <|← whnfCore r l cheapRec cheapProj
  | .letE _ _ val body _ =>
    save <|← whnfCore (body.instantiate1 val) l cheapRec cheapProj
  | .proj _ idx s =>
    if let some m ← reduceProj idx s cheapRec cheapProj then
      save <|← whnfCore m l cheapRec cheapProj
    else
      save e

def reduceExt (e : Expr) (d : Level × Expr) (dbg : Bool := false) : RecMO U (Option Expr) := do
  let (l, T) := d
  let getVars := do
    let sMvar ← mkFreshExprMVar T
    let tEqs := mkAppN (.const `Eq [l]) #[T, e, sMvar]
    let eqMvar ← mkFreshExprMVar tEqs
    pure (eqMvar, [sMvar])
  if let some (_, ts) ← extMatch getVars ``ldrw (Lean.Meta.DfEq.rwExt.getState (← readThe Context).env') dbg then 
    return .some ts[0]!
  return none

def ext : Bool := true

def whnfCore' (e : Expr) (l : Option (Level × Expr) := none) (cheapRec := false) (cheapProj := false) : RecMO T Expr := do
  let l ← l.getDM (getTypeInfo e)
  let e' ← whnfCoreNoExt' e l cheapRec cheapProj
  let dbg := 
    -- if let (.app (.app (.const ``Nat.add []) (.const ``Nat.zero [])) (.fvar a)) := e then
    --   true
    -- else
      false
  -- if dbg then
  --   dbg_trace s!"DBG[376]: TypeChecker.lean:484 {e'}"
  if ext then
    ext_trace do pure s!"DBG[1]: TypeChecker.lean:345: e'={← ppExpr e'}"
    if let .some e' ← reduceExt e' l dbg then
      whnfCore e' l cheapRec cheapProj
    else
      pure e'
  else
    pure e'

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

def reduceNative (_env : Kernel.Environment) (e : Expr) : EIO KernelException (Option Expr) := do
  let .app f (.const c _) := e | return none
  if f == .const ``reduceBool [] then
    throw <| .other s!"lean4lean does not support 'reduceBool {c}' reduction"
  else if f == .const ``reduceNat [] then
    throw <| .other s!"lean4lean does not support 'reduceNat {c}' reduction"
  return none

def rawNatLitExt? (e : Expr) : Option Nat := if e == .natZero then some 0 else e.rawNatLit?

def reduceBinNatOp (f : Nat → Nat → Nat) (a b : Expr) : RecMO T (Option Expr) := do
  let some v1 := rawNatLitExt? (← whnf a) | return none
  let some v2 := rawNatLitExt? (← whnf b) | return none
  return some <| .lit <| .natVal <| f v1 v2

def reduceBinNatPred (f : Nat → Nat → Bool) (a b : Expr) : RecMO T (Option Expr) := do
  let some v1 := rawNatLitExt? (← whnf a) | return none
  let some v2 := rawNatLitExt? (← whnf b) | return none
  return toExpr <| f v1 v2

def reduceNat (e : Expr) : RecMO T (Option Expr) := do
  if e.hasFVar then return none
  let nargs := e.getAppNumArgs
  if nargs == 1 then
    let f := e.appFn!
    if f == .const ``Nat.succ [] then
      let some v := rawNatLitExt? (← whnf e.appArg!) | return none
      return some <| .lit <| .natVal <| v + 1
  else if nargs == 2 then
    let .app (.app (.const f _) a) b := e | return none
    if f == ``Nat.add then return ← reduceBinNatOp Nat.add a b
    if f == ``Nat.sub then return ← reduceBinNatOp Nat.sub a b
    if f == ``Nat.mul then return ← reduceBinNatOp Nat.mul a b
    if f == ``Nat.pow then return ← reduceBinNatOp Nat.pow a b
    if f == ``Nat.gcd then return ← reduceBinNatOp Nat.gcd a b
    if f == ``Nat.mod then return ← reduceBinNatOp Nat.mod a b
    if f == ``Nat.div then return ← reduceBinNatOp Nat.div a b
    if f == ``Nat.beq then return ← reduceBinNatPred Nat.beq a b
    if f == ``Nat.ble then return ← reduceBinNatPred Nat.ble a b
  return none

def whnf' (_e : Expr) (l : Option (Level × Expr)) : RecMO T Expr := do
  let e ← whnfCore _e l
  -- Do not cache easy cases
  match e with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .lit .. => return e
  | .mdata _ e => return ← whnf e l
  | _ => pure ()

  match e with
  | .fvar id =>
    if !isLetFVar (← getLCtx) id then
      return e
  | .lam .. | .app .. | .const .. | .letE .. | .proj .. => pure ()
  | _ => unreachable!
  -- check cache
  if let some r := (← get).whnfCache[e]? then
    return r
  let rec loop t
  | 0 => throw .deterministicTimeout
  | fuel+1 => do
    let env ← getKEnv
    let t ← whnfCore' t l
    if let some t ← reduceNative env t then return t
    if let some t ← reduceNat t then return t
    let some t := unfoldDefinition env t | return t
    loop t fuel
  let r ← loop e 1000
  modify fun s => { s with whnfCache := s.whnfCache.insert e r }
  return r

def isDefEqLambda (t s : Expr) (subst : Array Expr := #[]) : RecMO T Bool :=
  match t, s with
  | .lam _ tDom tBody _, .lam name sDom sBody bi => do
    let sType ← if tDom != sDom then
      let sType := sDom.instantiateRev subst
      let tType := tDom.instantiateRev subst
      if !(← isDefEqCheckTypes 17 tType sType) then return false
      pure (some sType)
    else pure none
    let sType := sType.getD (sDom.instantiateRev subst)
    let id := ⟨← mkFreshId⟩
    withLCtx ((← getLCtx).mkLocalDecl id name sType bi) do
      isDefEqLambda tBody sBody (subst.push (.fvar id))
  | t, s => isDefEqCheckTypes 18 (t.instantiateRev subst) (s.instantiateRev subst)

def isDefEqForall (t s : Expr) (subst : Array Expr := #[]) : RecMO T Bool :=
  match t, s with
  | .forallE _ tDom tBody _, .forallE name sDom sBody bi => do
    let sType ← if tDom != sDom then
        let sType := sDom.instantiateRev subst
        let tType := tDom.instantiateRev subst
        if !(← isDefEqCheckTypes 19 tType sType) then return false
        pure (some sType)
      else pure none
    let cont := do
      let sType := sType.getD (sDom.instantiateRev subst)
      let id := ⟨← mkFreshId⟩
      withLCtx ((← getLCtx).mkLocalDecl id name sType bi) do
        isDefEqForall tBody sBody (subst.push (.fvar id))
    -- if let .app (.const ``localDfEq []) _ := sDom then
    --   let sType := sType.getD (sDom.instantiateRev subst)
    --   let localDfEq := sType.appArg!
    --   withLocalDfEq localDfEq do
    --     cont
    -- else
    --   cont
    cont
  | t, s => isDefEqCheckTypes 20 (t.instantiateRev subst) (s.instantiateRev subst)

def quickIsDefEq (t s : Expr) (l : Level) (T : Expr) (useHash := false) : RecMO U LBool := do
  if ← modifyGet fun (.mk a1 a2 a3 a4 a5 a6 a7 (eqvManager := m)) =>
    let (b, m) := m.isEquiv useHash t s
    (b, .mk a1 a2 a3 a4 a5 a6 a7 (eqvManager := m))
  then return .true
  match t, s with
  | .lam .., .lam .. => toLBoolM <| isDefEqLambda t s
  | .forallE .., .forallE .. => toLBoolM <| isDefEqForall t s
  | .sort a1, .sort a2 => pure (a1.isEquiv a2).toLBool
  | .mdata _ a1, .mdata _ a2 => toLBoolM <| isDefEq 4 a1 a2 l T
  | .lit a1, .lit a2 => pure (a1 == a2).toLBool
  | _, _ => return .undef

def isDefEqArgs (t s : Expr) : RecMO T Bool := do
  match t, s with
  | .app tf ta, .app sf sa =>
    if !(← isDefEqCheckTypes 21 ta sa) then return false
    isDefEqArgs tf sf
  | .app .., _ | _, .app .. => return false
  | _, _ => return true

def tryEtaExpansionCore (t s : Expr) (l : Level) (T : Expr) : RecMO U Bool := do
  if t.isLambda && !s.isLambda then
    let .forallE name ty _ bi ← whnf T | return false
    isDefEq 5 t (.lam name ty (.app s (.bvar 0)) bi) l T
  else return false

def tryEtaExpansion (t s : Expr) (l : Level) (T : Expr) : RecMO U Bool :=
  tryEtaExpansionCore t s l T <||> tryEtaExpansionCore s t l T

def tryEtaStructCore (t s : Expr) : RecMO T Bool := do
  let .const f _ := s.getAppFn | return false
  let env ← getKEnv
  let .ctorInfo fInfo ← env.get f | return false
  unless s.getAppNumArgs == fInfo.numParams + fInfo.numFields do return false
  unless isStructureLike' env fInfo.induct do return false
  let args := s.getAppArgs
  for h : i in [fInfo.numParams:args.size] do
    unless ← isDefEqCheckTypes 22 (.proj fInfo.induct (i - fInfo.numParams) t) args[i] do return false
  return true

def tryEtaStruct (t s : Expr) : RecMO T Bool :=
  tryEtaStructCore t s <||> tryEtaStructCore s t

def isDefEqApp (n : Nat) (t s : Expr) : RecMO T Bool := do
  unless t.isApp && s.isApp do return false
  t.withApp fun tf tArgs =>
  s.withApp fun sf sArgs => do
  unless tArgs.size == sArgs.size do return false
  unless ← isDefEqCheckTypes (1000 + n) tf sf do return false
  for ta in tArgs, sa in sArgs do
    unless ← isDefEqCheckTypes (2000 + n) ta sa do return false
  return true

def isDefEqProofIrrel (T : Expr) : RecMO U LBool := do
  if !(← isProp T) then return .undef
  return .true

def failedBefore (failure : Std.HashSet (Expr × Expr)) (t s : Expr) : Bool :=
  if t.hash < s.hash then
    failure.contains (t, s)
  else if t.hash > s.hash then
    failure.contains (s, t)
  else
    failure.contains (t, s) || failure.contains (s, t)

def cacheFailure (t s : Expr) : M Unit := do
  let k := if t.hash ≤ s.hash then (t, s) else (s, t)
  modify fun st => { st with failure := st.failure.insert k }

def tryUnfoldProjApp (e : Expr) (l : Level × Expr) : RecMO T (Option Expr) := do
  let f := e.getAppFn
  if !f.isProj then return none
  let e' ← whnfCore e l
  return if e' != e then e' else none

def lazyDeltaReductionStep (tn sn : Expr) (l : Level) (T : Expr) : RecMO U ReductionStatus := do
  let env ← getKEnv
  let delta e := whnfCore (unfoldDefinition env e).get! (cheapProj := true)
  let cont tn sn :=
    return match ← quickIsDefEq tn sn l T with
    | .undef => .continue tn sn
    | .true => .bool true
    | .false => .bool false
  match isDelta env tn, isDelta env sn with
  | none, none => return .unknown tn sn
  | some _, none =>
    if let some sn' ← tryUnfoldProjApp sn (l, T) then
      cont tn sn'
    else
      cont (← delta tn) sn
  | none, some _ =>
    if let some tn' ← tryUnfoldProjApp tn (l, T) then
      cont tn' sn
    else
      cont tn (← delta sn)
  | some dt, some ds =>
    let ht := dt.hints
    let hs := ds.hints
    if ht.lt' hs then
      cont tn (← delta sn)
    else if hs.lt' ht then
      cont (← delta tn) sn
    else
      if tn.isApp && sn.isApp && (unsafe ptrEq dt ds) && dt.hints.isRegular
        && !failedBefore (← get).failure tn sn
      then
        if Level.isEquivList tn.getAppFn.constLevels! sn.getAppFn.constLevels! then
          if ← isDefEqArgs tn sn then
            return .bool true
        cacheFailure tn sn
      cont (← delta tn) (← delta sn)

@[inline] def isNatZero (t : Expr) : Bool :=
  t == .natZero || t matches .lit (.natVal 0)

def isNatSuccOf? : Expr → Option Expr
  | .lit (.natVal (n+1)) => return .lit (.natVal n)
  | .app (.const ``Nat.succ _) e => return e
  | _ => none

def isDefEqOffset (t s : Expr) : RecMO T LBool := do
  if isNatZero t && isNatZero s then
    return .true
  match isNatSuccOf? t, isNatSuccOf? s with
  | some t', some s' => toLBoolM <| isDefEqCore 8 t' s' 1 (.const `Nat [])
  | _, _ => return .undef

def lazyDeltaReduction (tn sn : Expr) (l : Level) (T : Expr) : RecMO U ReductionStatus := loop tn sn 1000 where
  loop tn sn
  | 0 => throw .deterministicTimeout
  | fuel+1 => do
    let r ← isDefEqOffset tn sn
    if r != .undef then return .bool (r == .true)
    if !tn.hasFVar && !sn.hasFVar then
      if let some tn' ← reduceNat tn then
        return .bool (← isDefEqCore 9 tn' sn l T)
      else if let some sn' ← reduceNat sn then
        return .bool (← isDefEqCore 10 tn sn' l T)
    let env ← getKEnv
    if let some tn' ← reduceNative env tn then
      return .bool (← isDefEqCore 11 tn' sn l T)
    else if let some sn' ← reduceNative env sn then
      return .bool (← isDefEqCore 12 tn sn' l T)
    match ← lazyDeltaReductionStep tn sn l T with
    | .continue tn sn => loop tn sn fuel
    | r => return r

def tryStringLitExpansionCore (t s : Expr) : RecMO T LBool := do
  let .lit (.strVal st) := t | return .undef
  let .app sf _ := s | return .undef
  unless sf == .const ``String.mk [] do return .undef
  toLBoolM <| isDefEqCore 13 (.strLitToConstructor st) s 1 (.const `String [])

def tryStringLitExpansion (t s : Expr) : RecMO T LBool := do
  match ← tryStringLitExpansionCore t s with
  | .undef => tryStringLitExpansionCore s t
  | r => return r

def isDefEqUnitLike (T : Expr) : RecMO U Bool := do
  let tType ← whnf T
  let .const I _ := tType.getAppFn | return false
  let env ← getKEnv
  let .inductInfo { isRec := false, ctors := [c], numIndices := 0, .. } ← env.get I
    | return false
  let .ctorInfo { numFields := 0, .. } ← env.get c | return false
  return true

def instantiateLevelParamsDecl (decl : LocalDecl) (paramNames : List Name) (lvls : List Level) : LocalDecl := match decl with
  | .cdecl index fvarId userName type bi kind => .cdecl index fvarId userName (type.instantiateLevelParams paramNames lvls) bi kind
  | .ldecl index fvarId userName type value nonDep kind => .ldecl index fvarId userName (type.instantiateLevelParams paramNames lvls) (value.instantiateLevelParams paramNames lvls) nonDep kind

def instantiateLevelParamsCtx (lctx : LocalContext) (paramNames : List Name) (lvls : List Level) : LocalContext :=
  {lctx with fvarIdToDecl := lctx.fvarIdToDecl.map fun d => instantiateLevelParamsDecl d paramNames lvls, decls := lctx.decls.map fun d? => d?.map fun d => instantiateLevelParamsDecl d paramNames lvls}

open Lean.Meta in
def isDefEqExt (t s : Expr) (l : Level) (T : Expr) : RecMO U LBool := do
  let getVars rev := do
    let eq := if rev then mkAppN (.const `Eq [l]) #[T, s, t] else mkAppN (.const `Eq [l]) #[T, t, s]
    let eqMvar ← mkFreshExprMVar eq
    pure (eqMvar, [])
  if let some (_, _) ← extMatch (getVars false) ``ldeq (DfEq.dfEqExt.getState (← readThe Context).env') then 
    return .true
  if let some (_, _) ← extMatch (getVars true) ``ldeq (DfEq.dfEqExt.getState (← readThe Context).env') then 
    return .true
  return .undef

def isDefEqCore' (n : Nat) (t s : Expr) (l : Level) (T : Expr) : RecMO U Bool := do
  -- let mut localRws := []
  -- for decl in (← readThe Context).lctx do
  --   if let .app (.const ``localRw []) _ := decl.type.getForallBody then
  --     localRws := localRws ++ [decl.toExpr]
  
  let mut dbg := false
  -- if let (.app (.app (.const ``Nat.add []) (.const ``Nat.zero [])) (.fvar a)) := s then
  --   if let .fvar b := t then
  --     if a == b then
  --       dbg_trace s!"DBG[364]: TypeChecker.lean:820 (after if let (.app (.const Nat.succ []) (.app …)"
  --       dbg := true
  -- if let .app (.app (.const `Nat.add []) z) y := t then
  --   sorry

    -- if localRws.length > 0 then
    --   if t.isApp && s.isApp then
    --     if let .const ``HAdd.hAdd _ := t.getAppFn then
    --       if let .const ``Nat.succ _ := s.getAppFn then
    --         true
    --       else false
    --     else false
    --   else false
    -- else false

  -- if dbg then
  --   dbg_trace s!"DBG[362]: TypeChecker.lean:474 {t}      {s}"
  let r ← quickIsDefEq t s l T (useHash := true)
  if r != .undef then return r == .true
  -- if dbg then
  --   dbg_trace s!"DBG[367]: TypeChecker.lean:840 (after if dbg then)"

  if !t.hasFVar && s.isConstOf ``true then
    if (← whnf t).isConstOf ``true then return true

  -- let elimLocalDfEq e :=  do
  --   if e.isApp then
  --     if let .const ``localDfEq [] := e.appFn! then
  --       whnfCore (unfoldDefinition (← getKEnv) e).get! (cheapProj := true)
  --     else
  --       pure e
  --   else
  --     pure e

  -- let tn ← elimLocalDfEq $ ← whnfCore t (cheapProj := true)
  -- let sn ← elimLocalDfEq $ ← whnfCore s (cheapProj := true)
  let tn ← whnfCore t (l, T) (cheapProj := true)
  let sn ← whnfCore s (l, T) (cheapProj := true)
  -- if dbg then
  --   dbg_trace s!"DBG[365]: TypeChecker.lean:857 {s}, {sn}"

  if !(unsafe ptrEq tn t && ptrEq sn s) then
    let r ← quickIsDefEq tn sn l T
    if r != .undef then return r == .true

  -- if dbg then
  --   dbg_trace s!"DBG[369]: TypeChecker.lean:866 (after if dbg then)"

  let r' ← isDefEqProofIrrel T

  if r' != .undef then
    -- if r' == .true then
    --   dbg_trace s!"DBG[216]: TypeChecker.lean:724 {reqs}"
    -- for lem in (Lean.Meta.DfEq.dfEqExt.getState ((← readThe Context).env')) do
    --   dbg_trace s!"DBG[205]: TypeChecker.lean:545 {lem}"
    -- dbg_trace s!"DBG[207]: {r}"
    return r' == .true

  -- if dbg then
  --   dbg_trace s!"DBG[370]: TypeChecker.lean:877 (after return r == .true)"

  if ext then
    let r' ← isDefEqExt t s l T
    if r' != .undef then
      return r' == .true

  -- if dbg then
  --   dbg_trace s!"DBG[371]: TypeChecker.lean:884 (after return r == .true)"

  -- TODO integrate directed exteqs into lazy delta reduction
  match ← lazyDeltaReduction tn sn l T with
  | .continue .. => unreachable!
  | .bool b => return b
  | .unknown tn sn =>
  -- if dbg then
  --   dbg_trace s!"DBG[372]: TypeChecker.lean:893 (after | .unknown tn sn =>)"

  match tn, sn with
  | .const tf tl, .const sf sl =>
    if tf == sf && Level.isEquivList tl sl then return true
  | .fvar tv, .fvar sv => if tv == sv then return true
  | .proj _ ti te, .proj _ si se =>
    if ti == si then if ← isDefEqCheckTypes 25 te se then return true
  | _, _ => pure ()
  -- if dbg then
  --   dbg_trace s!"DBG[373]: TypeChecker.lean:903 (after | _, _ => pure ())"

  let tnn ← whnfCore tn (l, T)
  let snn ← whnfCore sn (l, T)
  if !(unsafe ptrEq tnn tn && ptrEq snn sn) then
    return ← isDefEqCore 14 tnn snn l T

  -- if dbg then
  --   dbg_trace s!"DBG[366]: TypeChecker.lean:897 (after if dbg then)"

  if ← isDefEqApp n tn sn then return true
  if ← tryEtaExpansion tn sn l T then return true
  if ← tryEtaStruct tn sn then return true
  let r ← tryStringLitExpansion tn sn
  if r != .undef then return r == .true
  if ← isDefEqUnitLike T then return true
  -- if dbg then
  --   dbg_trace s!"DBG[368]: TypeChecker.lean:909 {tn}, {sn}"
  return false

end Inner

open Inner

def Methods.withFuel : Nat → Methods
  | 0 =>
    { isDefEqCore := fun _ _ _ _ _ => throw .deepRecursion
      whnfCore := fun _ _ _ _ _ => throw .deepRecursion
      whnf := fun _ _ _ => throw .deepRecursion
      inferType := fun _ _ => throw .deepRecursion }
  | n + 1 =>
    { isDefEqCore := fun _n t s l T f => isDefEqCore' _n t s l T (fun a => f a) (withFuel n)
      whnfCore := fun e l r p f => whnfCore' e l r p (fun e => f e) (withFuel n)
      whnf := fun e l f => whnf' e l (fun e => f e) (withFuel n)
      inferType := fun e i f => inferType' e i (fun a => f a) (withFuel n) }

def RecM.run (x : RecM α) : M α := x (Methods.withFuel 1000)

def check (e : Expr) (lps : List Name) : M Expr :=
  withReader ({ · with lparams := lps }) (inferType e (inferOnly := false)).run'.run

def whnf (e : Expr) : M Expr := (Inner.whnf e).run'.run

def inferType (e : Expr) : M Expr := (Inner.inferType e).run'.run

def isDefEqCheckTypes' (n : Nat) (lps : List Name) (t s : Expr) : M Bool :=
  withReader ({ · with lparams := lps }) (Inner.isDefEqCheckTypes n t s).run'.run

def isDefEqCheckTypes (lps : List Name) (t s : Expr) : M Bool :=
  withReader ({ · with lparams := lps }) (Inner.isDefEqCheckTypes 26 t s).run'.run

def isDefEq (t s : Expr) (l : Level) (T : Expr) : M Bool := (Inner.isDefEq 7 t s l T).run'.run

def isProp (t : Expr) : M Bool := (Inner.isProp t).run'.run

def ensureSort (t : Expr) (s := t) : M Expr := (ensureSortCore t s).run'.run

def ensureForall (t : Expr) (s := t) : M Expr := (ensureForallCore t s).run'.run

def ensureType (e : Expr) : M Expr := do ensureSort (← inferType e) e

def etaExpand (e : Expr) : M Expr :=
  let rec loop fvars
  | .lam name dom body bi => do
    let d := dom.instantiateRev fvars
    let id := ⟨← mkFreshId⟩
    withLCtx ((← getLCtx).mkLocalDecl id name d bi) do
      let fvars := fvars.push (.fvar id)
      loop fvars body
  | it => do
    let itType ← whnf <| ← inferType <| it.instantiateRev fvars
    if !itType.isForall then return e
    let rec loop2 fvars args
    | 0, _ => throw .deepRecursion
    | fuel + 1, .forallE name dom body bi => do
      let d := dom.instantiateRev fvars
      let id := ⟨← mkFreshId⟩
      withLCtx ((← getLCtx).mkLocalDecl id name d bi) do
        let arg := .fvar id
        let fvars := fvars.push arg
        let args := args.push arg
        loop2 fvars args fuel <| ← whnf <| body.instantiate1 arg
    | _, it => return (← getLCtx).mkLambda fvars (mkAppN it args)
    loop2 fvars #[] 1000 itType
  loop #[] e

@[export lean_kernel_is_def_eq_new]
def isDefEqK (n : Nat) (lps : List Name) (env : Lean.Environment) (lctx : LocalContext) (a b : Expr) (fuel : Nat) (localDfEqs : List Expr) (options : Options) : EIO Kernel.Exception Bool :=
  M.run env.toKernelEnv env (lctx := lctx) (localDfEqs := localDfEqs) (safety := DefinitionSafety.safe) (fuel := fuel) (options := options) do
    TypeChecker.isDefEqCheckTypes' (500 + n) lps a b

@[export lean_kernel_check_new]
def checkK (n : Nat) (lps : List Name) (env : Lean.Environment) (lctx : LocalContext) (t : Expr) (options : Options) : EIO Kernel.Exception Expr :=
  M.run env.toKernelEnv env (lctx := lctx) (safety := DefinitionSafety.safe) (options := options) do
    TypeChecker.check t lps

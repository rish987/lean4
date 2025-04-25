import Lean4Lean.RecM

namespace Lean.TypeChecker.Inner

def toKernelException (m : EIO Exception α) : EIO KernelException (Sum α Exception) := fun x =>
  match m x with
  | .ok s I => .ok (.inl s) I
  | .error e I => .ok (.inr e) I

def runMetaM (m : MetaM T) : RecM T := do
  let mut options := (← readThe Context).options.insert `pp.explicit true |>.insert `pp.universes true
  let m' := Lean.Meta.MetaM.run m {lctx := ← getLCtx} {mctx := ← getMCtx}|>.run {options := options, fileName := default, fileMap := default, maxHeartbeats := 0} {env := (← readThe Context).env'}
  match ← toKernelException m' with
  | .inl ((reqs, _), _) => pure reqs
  | .inr (.internal _ _) => throw $ .other "untranslated Exception.Internal"
  | .inr (.error _ d) => throw $ .other (← d.toString)

def ppExpr (e : Expr) : RecM Format := runMetaM (Lean.Meta.ppExpr e)

def ext_trace (dbg : Bool) (getS : RecM String) : RecM Unit := do
  let mut print := dbg
  if let .some (.ofBool true) := (← getOptions).find `trace.Kernel.ext then
    print := true
  if print then
    dbg_trace (← getS)

def isExprDefEq (pattern : Expr) (target : Expr) (targetD : Option (Level × Expr) := none) (dbg := false) : RecM Bool := do
  let rec checkTypesAndAssign (mvar : Expr) (v : Expr) : RecM Bool := do
    if !mvar.isMVar then
      -- trace[Meta.isDefEq.assign.checkTypes] "metavariable expected"
      return false
    else
      -- must check whether types are definitionally equal or not, before assigning and returning true
      let vType ← inferType 1000 v let mvarType ← mvar.mvarId!.getType!
      -- TODO ? if there are no metavars, do the normal isDefEq check
      if (← isExprDefEq mvarType vType) then -- TODO correct to pass in here?
        -- dbg_trace s!"assigning {mvar} to {v}"
        mvar.mvarId!.assign v
        pure true
      else
        pure false
  termination_by sizeOf v
  decreasing_by
    sorry
  let rec processBinding (lctx : LocalContext) (fvars : Array Expr) (t s : Expr) : RecM Bool :=
    let process (n : Name) (d₁ d₂ b₁ b₂ : Expr) : RecM Bool := do
      let d₁     := d₁.instantiateRev fvars
      let d₂     := d₂.instantiateRev fvars
      if not (← isExprDefEq d₁ d₂) then
        return false
      let fvarId ← mkFreshId' 5
      let lctx   := lctx.mkLocalDecl fvarId n d₁
      let fvars  := fvars.push (mkFVar fvarId)
      withLCtx lctx do processBinding lctx fvars (← instantiateExprMVars b₁) (← instantiateExprMVars b₂)
    match t, s with
    | .forallE n d₁ b₁ _,    .forallE _ d₂ b₂ _    => process n d₁ d₂ b₁ b₂
    | .lam     n d₁ b₁ _,    .lam     _ d₂ b₂ _    => process n d₁ d₂ b₁ b₂
    | .letE    n d₁ v₁ b₁ _, .letE    _ d₂ v₂ b₂ _ => process n d₁ d₂ b₁ b₂ <&&> (do isExprDefEq (← instantiateExprMVars v₁) (← instantiateExprMVars v₂))
    | _,                  _                  =>
        isExprDefEq (t.instantiateRev fvars) (s.instantiateRev fvars)
  termination_by sizeOf t
  decreasing_by
    sorry
    sorry
    sorry
    sorry
  let tryMatch p t := do
    let wrapRestoreMctx f := do
      let mctx := (← get).mctx
      let ret ← f
      if ret != .true then
        modify fun s => {s with mctx}
      pure ret
    -- TODO TODO FIXME have to unset any assigned mvars on failure
    wrapRestoreMctx do
    match p, t with
    | .lam .., .lam ..
    | .forallE .., .forallE ..
    | .letE .., .letE .. => do
      let ret ← processBinding (← getLCtx) #[] p t
      pure ret
    | .sort a1, .sort a2 => pure (a1.isEquiv a2)
    | .mdata _ a1, _ => isExprDefEq a1 t targetD (dbg := dbg)
    | _, .mdata _ a2 => isExprDefEq p a2 targetD (dbg := dbg)
    | .lit a1, .lit a2 => pure (a1 == a2)
    | .proj n i s, .proj n' i' s' => pure (n == n') <&&> pure (i == i') <&&> isExprDefEq s s' (dbg := dbg)
    | .const n ls, .const n' ls' =>
      let ret := n == n' && (ls.zip ls').all (fun (l, l') => l.isEquiv l') -- TODO TODO FIXME need to assign level var metavars for universe-polymorphic extensionalmas?
      pure ret
    | .fvar id, .fvar id' => pure $ id == id'
    | .app f a, .app f' a' => do
      let feq ← isExprDefEq f f' (dbg := dbg)
      if not feq then return false
      let a ← instantiateMVars a
      let a' ← instantiateMVars a'
      -- dbg_trace s!"DBG[19]: Ext.lean:70 {f}, {a}, {f'}, {a'}"
      let aeq ← isExprDefEq a a' (dbg := dbg)
      pure $ feq && aeq
    | .bvar .., _ => unreachable!
    | _, .bvar .. => unreachable!
    | .mvar pm, .mvar tm =>
      let some pmd := (← getMCtx).findDecl? pm | unreachable!
      let some tmd := (← getMCtx).findDecl? tm | unreachable!
      if tmd.depth == (← getMCtx).depth then
        checkTypesAndAssign t p
      else if pmd.depth == (← getMCtx).depth then
        checkTypesAndAssign p t
      else
        pure $ pm == tm
    | _, .mvar tm => 
      let some tmd := (← getMCtx).findDecl? tm | unreachable!
      if tmd.depth == (← getMCtx).depth then
        checkTypesAndAssign t p
      else
        pure false
    | .mvar pm, _ =>
      let some pmd := (← getMCtx).findDecl? pm | unreachable!
      if pmd.depth == (← getMCtx).depth then
        checkTypesAndAssign p t
      else
        pure false
    | _, _ =>
      pure false

  if ← tryMatch pattern target then
    return true

  let mut target' ← whnfCoreNoExt 10061 target
  if target' != target then
    if ← tryMatch pattern target' then
      return true
  -- let targetD ← targetD.getDM $ getTypeInfo target'

  while true do
    -- target' ← pure target'
    --
    -- let newTarget? ← do
    --   dbg_trace s!"DBG[15]: Ext.lean:101: target'={target'}"
    --   if let some newTarget ← reduceExt 1 target' (deep := false) then
    --     pure $ .some newTarget
    --   else if let some newTarget := unfoldDefinition (← getKEnv) target' then
    --     pure $ .some newTarget
    --   else pure .none
    --
    -- if let some newTarget := newTarget? then
    if let some newTarget := unfoldDefinition (← getKEnv) target' then
      target' ← whnfCoreNoExt 1006 newTarget
      -- target' ← pure newTarget
      if ← tryMatch pattern target' then return true
    else break

  ext_trace dbg do pure s!"DBG[409]: Ext.lean:98: target={pattern}"
  let mut pattern' ← whnfCore 10071 pattern
  ext_trace dbg do pure s!"DBG[409']: Ext.lean:98: target={pattern}"
  if pattern' != pattern then
    if ← tryMatch pattern' target then -- TODO should use target' instead?
      return true
  -- let d := if let .app (.const `Nat.succ []) (.mvar ..) := pattern then true else false
  let d := if let .app (Expr.const `Nat.succ []) (Expr.const `Nat.zero []) := target then true else false

  let mut i := 0
  while true do
    i := i + 1
    ext_trace dbg do pure s!"DBG[413]: reduction step {i} on {pattern}"
    if let some newPattern := unfoldDefinition (← getKEnv) pattern' then
      pattern' ← whnfCore 1007 newPattern
      -- target' ← pure newTarget
      if ← tryMatch pattern' target then return true
    else break

  pure false
  termination_by sizeOf target
  decreasing_by
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry
    sorry

def mkFreshExprMVar (type : Expr) (kind : MetavarKind := default) (userName : Name := default) : RecM Expr := do
  Lean.Meta.mkFreshExprMVarAt (← getLCtx) #[] type kind userName

def forallMetaTelescope (e : Expr) : RecM (Array Expr × Expr) :=
  process #[] e
where
  process (mvars : Array Expr) (type : Expr) : RecM (Array Expr × Expr) := do
    match type with
    | .forallE n d b _ =>
      let d  := d.instantiateRev mvars
      let mvar ← mkFreshExprMVar d default n
      let mvars := mvars.push mvar
      process mvars b
    | _ =>
      let type := type.instantiateRev mvars
      return (mvars, type)

def forallTelescope
    (type              : Expr)
    (k                 : Array Expr → Expr → RecM α) : RecM α := do
  let rec process (lctx : LocalContext) (fvars : Array Expr) (j : Nat) (type : Expr) : RecM α := do
    match type with
    | .forallE n d b bi =>
      let d     := d.instantiateRevRange j fvars.size fvars
      let fvarId ← mkFreshId' 5
      let lctx  := lctx.mkLocalDecl fvarId n d bi
      let fvar  := mkFVar fvarId
      let fvars := fvars.push fvar
      process lctx fvars j b
    | _ =>
      let type := type.instantiateRevRange j fvars.size fvars;
      withLCtx lctx do
        k fvars type
  process (← getLCtx) #[] 0 type

variable {m : Type → Type u} [Monad m] [MonadMCtx m] 

def withNewMCtxDepth(x : RecM α) : RecM α := do
  let saved ← get
  modify fun s => { s with mctx := s.mctx.incDepth false }
  try
    x
  finally
    modify fun s => { s with mctx := saved.mctx }

def apply (mvarId : MVarId) (e : Expr) (eType? : Option Expr := none) (dbg := false) (skipLem : Name ⊕ FVarId) : RecM (Option (Array MVarId)) := do
  let some targetType ← mvarId.getType? (m := RecM) | unreachable!
  let eType ← eType?.getDM (inferType 1001 e)

  -- let rec getNumArgs e := do match e with
  -- | .forallE _ _ b _ => pure $ 1 + (← getNumArgs b)
  -- | _ => pure 0
  -- let numArgs ← getNumArgs eType
  -- let targetTypeNumArgs ← getNumArgs targetType
  -- assert! targetTypeNumArgs == 0

  let newMVars : Array Expr ← do
    let (newMVars, eType) ← forallMetaTelescope eType
    -- ext_trace dbg do pure s!"DBG[411]: Ext.lean:226 {eType}"
    if not (← withExtLemReducing skipLem $ isExprDefEq eType targetType) then
      return none
    else
      -- for mvar in newMVars do
      --   ext_trace dbg do pure s!"DBG[]: {mvar}: {← mvar.mvarId!.isAssigned}"
      pure newMVars

  -- postprocessAppMVars `apply mvarId newMVars binderInfos cfg.synthAssignedInstances cfg.allowSynthFailures
  assert! not e.hasMVar
  mvarId.assign (mkAppN e newMVars)
  let newMVars ← newMVars.filterM fun mvar => do pure $ (← instantiateMVars mvar) == mvar
  let newMVarIds := newMVars.map fun m => m.mvarId!
  return newMVarIds

def getExtLemmaNames (rw : Bool) : RecM (List Name × List FVarId) := do
  let env' := (← readThe Context).env'
  let extLems := if rw then
    (Lean.Meta.DfEq.rwExt.getState env')
  else
    (Lean.Meta.DfEq.dfEqExt.getState env')

  let extHypMarker := if rw then ``ldrw else ``ldeq
  let mut extHyps : List FVarId := []
  for decl in (← getLCtx) do
    -- if let .some (.inr lemFid) := skipLem? then
    --   if decl.fvarId == lemFid then
    --     continue
    -- if dbg then 
    --   dbg_trace s!"Checking: {decl.userName} : {← ppExpr decl.type}"
    if let .app (.const n []) _ := decl.type.getForallBody then -- TODO remove once we can generate lemmas for intermediate reducts
      if n == extHypMarker then
        extHyps := extHyps ++ [decl.fvarId]

  let extLemsReducing := (← readThe Context).extLemsReducing
  pure (extLems.filter (fun id => not $ extLemsReducing.contains (.inl id)), extHyps.filter (fun id => not $ extLemsReducing.contains (.inr id)))

structure ExtLemmData where
name : Name
info : ConstantInfo

structure ExtHypData where
id : FVarId
type : Expr

inductive ExtData where
| lem : ExtLemmData → ExtData
| hyp : ExtHypData → ExtData

def getExtLemmas (typ : Expr) (localMarker : Name) (extLemHypNames : List Name × List FVarId) (dbg := false) : RecM (List ExtData) := do
  let (extLemNames, extHypNames) := extLemHypNames

  let mut extHyps := []
  for extHypName in extHypNames do
    let decl := (← getLCtx).get! extHypName
    -- if let .some (.inr lemFid) := skipLem? then
    --   if decl.fvarId == lemFid then
    --     continue
    -- if dbg then 
    --   dbg_trace s!"Checking: {decl.userName} : {← ppExpr decl.type}"
    if let .app (.const n []) _ := decl.type.getForallBody then -- TODO remove once we can generate lemmas for intermediate reducts
      if n == localMarker then
        let d? ← forallTelescope decl.type fun vs b => do
          let newType := (← getLCtx).mkForall vs b.appArg!
          let .app (.app (.app (.const `Eq [_]) T) _) _ := b.appArg! | throw $ .other s!"type of extensional hypothesis {decl.userName} not of expected form: {decl.type}"
          let id := decl.fvarId
          if not (← isDefEqCore 0 typ T) then -- TODO FIXME handle case where T contains fvars
            pure none
          else
            pure $ .some $ .hyp {id, type := newType}
        if let some d := d? then 
          extHyps := extHyps ++ [d]
        if dbg then 
          dbg_trace s!"Added: {decl.userName} : {← ppExpr decl.type}"

  -- if let .some (.inl lemName) := skipLem? then
  --   lems := lems.filter (· != lemName)
  let mut extLems := []
  for extLemName in extLemNames do
    let some info := (← getKEnv).find? extLemName | throw $ .other s!"failed to find extensional lemma {extLemName} in environment"
    let d? ← forallTelescope info.type fun vs b => do
      let .app (.app (.app (.const `Eq [_]) T) _) _ := b | throw $ .other s!"type of extensional lemma {info.name} not of expected form: {info.type}"
      let name := info.name
      if not (← isDefEqCore 0 typ T) then -- TODO FIXME handle case where T contains fvars
        pure none
      else
        -- pure $ .some $ .hyp {name}(((id, ← Lean.Meta.mkConstWithFreshMVarLevels' info), none), false)
        pure $ .some $ .lem {name, info}
    if let some d := d? then 
      extLems := extLems ++ [d]
  -- let mut candidates : List ((((Name ⊕ FVarId) × Expr) × Option Expr) × Bool):= (← lemInfos.mapM (fun i => do pure (.inl i.name, ← Lean.Meta.mkConstWithFreshMVarLevels' i))).zip (List.replicate lems.length none) |>.zip (lems.map (fun n => n == `x))
  pure $ extLems ++ extHyps

def extMatch' (typ : Expr) (getTs : (List (List Expr → Expr))) (localMarker : Name) (lems : List Name) (dbg := false) (skipLem? : Option (Name ⊕ FVarId)) : RecM (Option (Expr × List Expr)) := do
  if (← readThe Context).fuel == 0 then
    return none
  -- options := options.insert `trace.Meta.isDefEq (.ofBool true)
  -- let localDfEqs := (← readThe Context).localDfEqs
  -- if dbg then 
  --   dbg_trace s!"DBG[387]: TypeChecker.lean:406 (after if dbg then)"

  let ret? ← (do
    let candidates ← sorry
    -- TODO append to extLemsReducing when trying to match on an extensional lemma
    let tryExtEq lem type? (T : Expr) (ts : List Expr) (dbg : Bool) (skipLem : Name ⊕ FVarId) : RecM (Option (Expr × List Expr)) := do
      let condString := do pure s!"{← ppExpr $ ← T.mvarId!.getType!}"
      ext_trace dbg do pure s!"Trying to apply (fuel {(← readThe Context).fuel}): {← ppExpr $ lem} : {← ppExpr $ (← inferType 1002 lem)} to {← condString}"
      let some gs ← apply T.mvarId! lem type? dbg skipLem |
        ext_trace dbg do pure s!"Applying FAIL: {← ppExpr $ lem} : {← ppExpr $ (← inferType 1003 lem)} to {← condString}"
        -- if dbg then
        --   dbg_trace s!"Applying FAIL: {← ppExpr $ lem} : {← ppExpr $ (← Meta.inferType lem)} to {← condString}"
        return none

      ext_trace dbg do pure s!"Applying OK ({gs.size}):{← ppExpr $ (← inferType 1004 lem)} to  {← condString}" --"\n  {← gs.mapM (fun (id : MVarId) => do ppExpr $ ← id.getType)}\n  {← localLems.mapM (do ppExpr $ ← Meta.inferType ·.1)}"
      -- if dbg then
      --   dbg_trace s!"Applying OK:{← ppExpr $ (← Meta.inferType lem)} to  {← condString}" --"\n  {← gs.mapM (do ppExpr $ ← ·.getType)}\n  {← localLems.mapM (do ppExpr $ ← Meta.inferType ·.1)}"
      for g in gs do
        let gT ← g.getType!
        let .app (.app (.app (.const `Eq [l]) T) lhs) rhs := gT | throw $ .other s!"type of extensional hypothesis {g.name} not of expected form: {gT}"
        ext_trace dbg do pure s!"Trying reflection: {← ppExpr $ ← g.getType!}"
        if not (← isDefEqCore 999 lhs rhs) then
          ext_trace dbg do pure s!"Reflection FAIL: {← ppExpr $ ← g.getType!}"
          return none
        let prf := mkAppN (.const `Eq.refl [l]) #[T, lhs]
        g.assign prf
        ext_trace dbg do pure s!"Reflection OK: {← ppExpr $ ← g.getType!}"
      ext_trace dbg do pure s!"Showing OK: {← ppExpr $ ← T.mvarId!.getType!}"
      let TInst ← instantiateMVars T
      let tsInst ← ts.mapM (fun t => instantiateMVars t)
      return some (TInst, tsInst)

    let getMVars := do
      let ts ← getTs.foldlM (init := []) fun acc f => do
        let mT := f acc
        let m ← mkFreshExprMVar mT
        pure $ acc ++ [m]
      let T::ts := ts.reverse | unreachable!
      pure (T, ts)

    let (T, _) ← getMVars
    let condString := do pure s!"{← ppExpr $ ← T.mvarId!.getType!}"
    -- let dbg := (← readThe Core.Context).options.get? `trace.Kernel.ext
    ext_trace dbg do pure s!"Trying to show {← condString}"

    for (((skipLem, lem), type?), dbg) in candidates do
      let prf? ← withNewMCtxDepth $ do
        let (T, ts) ← getMVars
        -- for eqMvar in [tEqsMvar, sEqtMvar] do
        -- TODO is there a way to "undo" assignments from previous failed unification attempts,
        -- rather than making new mvars every time?
        tryExtEq lem type? T ts dbg skipLem
      if let some prf := prf? then
        return some prf
    ext_trace dbg do pure s!"Showing FAIL: {← ppExpr $ ← T.mvarId!.getType!}"
    return none
    )

  if let some (prf, ts) := ret? then
    -- if prf.hasExprMVar then -- FIXME put these back, but only consider mvars at the current depth
    --   throw $ .other s!"unexpected mvar found in extensional equality proof: {prf}"
    -- if ts.any (·.hasExprMVar) then
    --   throw $ .other "unexpected mvar found in extensionally assigned variable"

    -- check that the proof returned by unification is well-typed with the kernel itself,
    -- to minimize the trust that we place on unification
    _ ← inferType 1005 prf (inferOnly := false)
    return some (prf, ts)

  return none

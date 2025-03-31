import Lean4Lean.RecM

namespace Lean.TypeChecker.Inner

def toKernelException (m : EIO Exception α) : EIO KernelException (Sum α Exception) := fun x =>
  match m x with
  | .ok s I => .ok (.inl s) I
  | .error e I => .ok (.inr e) I

def runMetaM (m : MetaM T) : RecMO U T := do
  let mut options := (← readThe Context).options
  let m' := Lean.Meta.MetaM.run m {lctx := ← getLCtx} {mctx := ← getMCtx}|>.run {options := options, fileName := default, fileMap := default, maxHeartbeats := 0} {env := (← readThe Context).env'}
  match ← toKernelException m' with
  | .inl ((reqs, _), _) => pure reqs
  | .inr (.internal _ _) => throw $ .other "untranslated Exception.Internal"
  | .inr (.error _ d) => throw $ .other (← d.toString)

def isExprDefEq (pattern : Expr) (target : Expr) (deep := false) : RecMO T Bool := do
  let rec checkTypesAndAssign (mvar : Expr) (v : Expr) : RecMO T Bool := do
    if !mvar.isMVar then
      -- trace[Meta.isDefEq.assign.checkTypes] "metavariable expected"
      return false
    else
      -- must check whether types are definitionally equal or not, before assigning and returning true
      let vType ← inferType v
      let mvarType ← mvar.mvarId!.getType!
      -- TODO ? if there are no metavars, do the normal isDefEq check
      if (← isExprDefEq mvarType vType) then
        mvar.mvarId!.assign v
        pure true
      else
        pure false
  termination_by sizeOf v
  decreasing_by
    sorry
  let rec processBinding (lctx : LocalContext) (fvars : Array Expr) (t s : Expr) : RecMO T Bool :=
    let process (n : Name) (d₁ d₂ b₁ b₂ : Expr) : RecMO T Bool := do
      let d₁     := d₁.instantiateRev fvars
      let d₂     := d₂.instantiateRev fvars
      if not (← isExprDefEq d₁ d₂) then
        return false
      let fvarId ← mkFreshFVarId
      let lctx   := lctx.mkLocalDecl fvarId n d₁
      let fvars  := fvars.push (mkFVar fvarId)
      processBinding lctx fvars (← instantiateExprMVars b₁) (← instantiateExprMVars b₂)
    match t, s with
    | .forallE n d₁ b₁ _,    .forallE _ d₂ b₂ _    => process n d₁ d₂ b₁ b₂
    | .lam     n d₁ b₁ _,    .lam     _ d₂ b₂ _    => process n d₁ d₂ b₁ b₂
    | .letE    n d₁ v₁ b₁ _, .letE    _ d₂ v₂ b₂ _ => process n d₁ d₂ b₁ b₂ <&&> (do isExprDefEq (← instantiateExprMVars v₁) (← instantiateExprMVars v₂))
    | _,                  _                  =>
      withLCtx lctx do
        isExprDefEq (t.instantiateRev fvars) (s.instantiateRev fvars)
  termination_by sizeOf t
  decreasing_by
    sorry
    sorry
    sorry
    sorry
  let tryMatch t := 
    match pattern, t with
    | .lam .., .lam ..
    | .forallE .., .forallE ..
    | .letE .., .letE .. => do processBinding (← getLCtx) #[] pattern target
    | .sort a1, .sort a2 => pure (a1.isEquiv a2)
    | .mdata _ a1, _ => isExprDefEq a1 target
    | _, .mdata _ a2 => isExprDefEq pattern a2
    | .lit a1, .lit a2 => pure (a1 == a2)
    | .proj n i s, .proj n' i' s' => pure (n == n') <&&> pure (i == i') <&&> isExprDefEq s s'
    | .const n ls, .const n' ls' =>
      let ret := n == n' && (ls.zip ls').all (fun (l, l') => l.isEquiv l')
      pure ret
    | .fvar id, .fvar id' => pure $ id == id'
    | .app f a, .app f' a' => do
      let feq ← isExprDefEq f f'
      let a ← instantiateMVars a
      let a' ← instantiateMVars a'
      -- dbg_trace s!"DBG[19]: Ext.lean:70 {f}, {a}, {f'}, {a'}"
      let aeq ← isExprDefEq a a'
      pure $ feq && aeq
    | .bvar .., _ => unreachable!
    | _, .bvar .. => unreachable!
    | .mvar .., .mvar ..
    | _, .mvar .. => 
      checkTypesAndAssign target pattern
    | .mvar .., _ =>
      checkTypesAndAssign pattern target
    | _, _ =>
      pure false

  if ← tryMatch target then
    return true
  let mut target' := target
  while true do
    if let some newTarget := unfoldDefinition (← getKEnv) target' then
      target' ← whnfCore newTarget
      if ← tryMatch target' then return true
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

def mkFreshExprMVar (type : Expr) (kind : MetavarKind := default) (userName : Name := default) : RecMO T Expr := do
  Lean.Meta.mkFreshExprMVarAt (← getLCtx) #[] type kind userName

def forallMetaTelescope (e : Expr) : RecMO T (Array Expr × Expr) :=
  process #[] e
where
  process (mvars : Array Expr) (type : Expr) : RecMO T (Array Expr × Expr) := do
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
    (k                 : Array Expr → Expr → RecMO T α) : RecMO T α := do
  let rec process (lctx : LocalContext) (fvars : Array Expr) (j : Nat) (type : Expr) : RecMO T α := do
    match type with
    | .forallE n d b bi =>
      let d     := d.instantiateRevRange j fvars.size fvars
      let fvarId ← mkFreshFVarId
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

def apply (mvarId : MVarId) (e : Expr) (eType? : Option Expr := none) : RecMO T (Option (Array MVarId)) := do
  let some targetType ← mvarId.getType? (m := RecMO T) | unreachable!
  let eType ← eType?.getDM (inferType e)

  -- let rec getNumArgs e := do match e with
  -- | .forallE _ _ b _ => pure $ 1 + (← getNumArgs b)
  -- | _ => pure 0
  -- let numArgs ← getNumArgs eType
  -- let targetTypeNumArgs ← getNumArgs targetType
  -- assert! targetTypeNumArgs == 0

  let newMVars : Array Expr ← do
    let (newMVars, eType) ← forallMetaTelescope eType
    if not (← isExprDefEq eType targetType) then
      return none
    else
      pure newMVars

  -- postprocessAppMVars `apply mvarId newMVars binderInfos cfg.synthAssignedInstances cfg.allowSynthFailures
  assert! not e.hasMVar
  mvarId.assign (mkAppN e newMVars)
  let newMVars ← newMVars.filterM fun mvar => not <$> mvar.mvarId!.isAssigned
  let newMVarIds := newMVars.map fun m => m.mvarId!
  return newMVarIds

def ppExpr (e : Expr) : RecMO T Format := runMetaM (Lean.Meta.ppExpr e)

def ext_trace (getS : RecMO T String) : RecMO T Unit := do
  if let .some (.ofBool true) := (← getOptions).find `trace.Kernel.ext then
    dbg_trace (← getS)

def extMatch' (getT : RecMO U (Expr × List Expr)) (localMarker : Name) (lems : List Name) (dbg := false) : RecMO U (Option (Expr × List Expr)) := do
  if (← readThe Context).fuel == 0 then
    return none
  -- options := options.insert `trace.Meta.isDefEq (.ofBool true)
  -- let localDfEqs := (← readThe Context).localDfEqs
  -- if dbg then 
  --   dbg_trace s!"DBG[387]: TypeChecker.lean:406 (after if dbg then)"

  let ret? ← (do
    let mut localLems := []
    for decl in (← getLCtx) do
      -- if dbg then 
      --   dbg_trace s!"Checking: {decl.userName} : {← ppExpr decl.type}"
      if let .app (.const n []) _ := decl.type.getForallBody then -- TODO remove once we can generate lemmas for intermediate reducts
        if n == localMarker then
          let newType ← forallTelescope decl.type fun vs b => do pure $ (← getLCtx).mkForall vs b.appArg!
          localLems := localLems ++ [(decl.toExpr, .some newType)]
          if dbg then 
            dbg_trace s!"Added: {decl.userName} : {← ppExpr decl.type}"

    let lemInfos ← lems.mapM (fun l => do
        let some info := (← getKEnv).find? l | throw $ .other s!"failed to find extensional lemma {l} in environment"
        pure info
      )
    let mut candidates := (← lemInfos.mapM (Lean.Meta.mkConstWithFreshMVarLevels' ·)).zip (List.replicate lems.length none)
    candidates := candidates ++ localLems
    let tryExtEq {U} lem type? (T : Expr) (ts : List Expr) : RecMO U (Option (Expr × List Expr)) := do
      let condString := do pure s!"{← ppExpr $ ← T.mvarId!.getType!}"
      -- let dbg := (← readThe Core.Context).options.get? `trace.Kernel.ext
      ext_trace do pure s!"Trying to show {← condString}"
      ext_trace do pure s!"Trying to apply (fuel {(← read).fuel}): {← ppExpr $ lem} : {← ppExpr $ (← inferType lem)} to {← condString}"
      let some gs ← apply T.mvarId! lem type? | 
        ext_trace do pure s!"Applying FAIL: {← ppExpr $ lem} : {← ppExpr $ (← inferType lem)} to {← condString}"
        -- if dbg then
        --   dbg_trace s!"Applying FAIL: {← ppExpr $ lem} : {← ppExpr $ (← Meta.inferType lem)} to {← condString}"
        return none

      ext_trace do pure s!"Applying OK:{← ppExpr $ (← inferType lem)} to  {← condString}" --"\n  {← gs.mapM (fun (id : MVarId) => do ppExpr $ ← id.getType)}\n  {← localLems.mapM (do ppExpr $ ← Meta.inferType ·.1)}"
      -- if dbg then
      --   dbg_trace s!"Applying OK:{← ppExpr $ (← Meta.inferType lem)} to  {← condString}" --"\n  {← gs.mapM (do ppExpr $ ← ·.getType)}\n  {← localLems.mapM (do ppExpr $ ← Meta.inferType ·.1)}"
      for g in gs do
        let gT ← g.getType!
        let .app (.app (.app (.const `Eq [l]) T) lhs) rhs := gT | throw $ .other s!"extensional hypothesis not of expected form: {gT}"
        ext_trace do pure s!"Trying reflection: {← ppExpr $ ← g.getType!}"
        if not (← isDefEqCore 999 lhs rhs l T) then
          ext_trace do pure s!"Reflection FAIL: {← ppExpr $ ← g.getType!}"
          return none
        ext_trace do pure s!"Reflection OK: {← ppExpr $ ← g.getType!}"
      ext_trace do pure s!"Showing OK: {← ppExpr $ ← T.mvarId!.getType!}"
      let TInst ← instantiateMVars T
      let tsInst ← ts.mapM (fun t => instantiateMVars t)
      return some (TInst, tsInst)

    for (lem, type?) in candidates do
      let (T, ts) ← getT
      -- for eqMvar in [tEqsMvar, sEqtMvar] do
      -- TODO is there a way to "undo" assignments from previous failed unification attempts,
      -- rather than making new mvars every time?
      if let .some prf ← tryExtEq lem type? T ts then
        return some prf
    let (T, _) ← getT
    ext_trace do pure s!"Showing FAIL: {← ppExpr $ ← T.mvarId!.getType!}"
    return none
    )

  if let some (prf, ts) := ret? then
    if prf.hasExprMVar then
      throw $ .other "unexpected mvar found in extensional equality proof"
    if ts.any (·.hasExprMVar) then
      throw $ .other "unexpected mvar found in extensionally assigned variable"
    -- check that the proof returned by unification is well-typed with the kernel itself,
    -- to minimize the trust that we place on unification
    _ ← inferType prf (inferOnly := false)
    return some (prf, ts)

  return none

def extMatch (getT : RecMO U (Expr × List Expr)) (localMarker : Name) (lems : List Name) (dbg := false) : RecMO U (Option (Expr × List Expr)) :=
  extMatch' getT localMarker lems dbg

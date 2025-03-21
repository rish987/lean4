import Lean4Lean.RecM

namespace Lean.TypeChecker.Inner

open Lean.Meta

def toKernelException (m : EIO Exception α) : EIO KernelException (Sum α Exception) := fun x =>
  match m x with
  | .ok s I => .ok (.inl s) I
  | .error e I => .ok (.inr e) I

private def checkTypesAndAssign (mvar : Expr) (v : Expr) : RecMO T Bool := do
  if !mvar.isMVar then
    trace[Meta.isDefEq.assign.checkTypes] "metavariable expected"
    return false
  else
    -- must check whether types are definitionally equal or not, before assigning and returning true
    let mvarType ← inferType mvar
    let vType ← inferType v
    if (← Meta.isExprDefEqAux mvarType vType) then
      mvar.mvarId!.assign v
      pure true
    else
      pure false

def isExprDefEqShallowImpl (t : Expr) (s : Expr) : RecMO T Bool :=
  let rec processBinding (lctx : LocalContext) (fvars : Array Expr) (t s : Expr) : RecMO T Bool :=
    let process (n : Name) (d₁ d₂ b₁ b₂ : Expr) : RecMO T Bool := do
      let d₁     := d₁.instantiateRev fvars
      let d₂     := d₂.instantiateRev fvars
      if not (← isExprDefEqShallowImpl d₁ d₂) then
        return false
      let fvarId ← mkFreshFVarId
      let lctx   := lctx.mkLocalDecl fvarId n d₁
      let fvars  := fvars.push (mkFVar fvarId)
      processBinding lctx fvars b₁ b₂
    match t, s with
    | .forallE n d₁ b₁ _,    .forallE _ d₂ b₂ _    => process n d₁ d₂ b₁ b₂
    | .lam     n d₁ b₁ _,    .lam     _ d₂ b₂ _    => process n d₁ d₂ b₁ b₂
    | .letE    n d₁ v₁ b₁ _, .letE    _ d₂ v₂ b₂ _ => isExprDefEqShallowImpl v₁ v₂ <&&> process n d₁ d₂ b₁ b₂
    | _,                  _                  =>
      withLCtx' lctx do
        isExprDefEqShallowImpl (t.instantiateRev fvars) (s.instantiateRev fvars)
  decreasing_by
    sorry
  match t, s with
  | .lam .., .lam ..
  | .forallE .., .forallE ..
  | .letE .., .letE .. => do processBinding (← getLCtx) #[] t s
  | .sort a1, .sort a2 => pure (a1.isEquiv a2)
  | .mdata _ a1, _ => isExprDefEqShallowImpl a1 s
  | _, .mdata _ a2 => isExprDefEqShallowImpl t a2
  | .lit a1, .lit a2 => pure (a1 == a2)
  | .proj n i s, .proj n' i' s' => pure (n == n') <&&> pure (i == i') <&&> isExprDefEqShallowImpl s s'
  | .const n ls, .const n' ls' => pure (n == n' && (ls.zip ls').all (fun (l, l') => l.isEquiv l'))
  | .fvar id, .fvar id' => pure $ id == id'
  | .app f a, .app f' a' => isExprDefEqShallowImpl f f' <&&> isExprDefEqShallowImpl a a'
  | .bvar .., _ => unreachable!
  | _, .bvar .. => unreachable!
  | .mvar .., .mvar .. => 
    checkTypesAndAssign s t
  | _, .mvar .. => 
    checkTypesAndAssign s t
  | .mvar .., _ =>
    checkTypesAndAssign t s
  | _, _ =>
    pure false

def apply (mvarId : MVarId) (e : Expr) (eType? : Option Expr := none) : RecMO T (List MVarId) := do
  mvarId.checkNotAssigned `apply
  let targetType ← mvarId.getType
  let eType      ← eType?.getDM (inferType e)
  let (numArgs, hasMVarHead) ← getExpectedNumArgsAux eType
  /-
  The `apply` tactic adds `_`s to `e`, and some of these `_`s become new goals.
  When `hasMVarHead` is `false` we try different numbers, until we find a type compatible with `targetType`.
  We used to try only `numArgs-targetTypeNumArgs` when `hasMVarHead = false`, but this is not always correct.
  For example, consider the following example
  ```
  example {α β} [LE_trans β] (x y z : α → β) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
    apply le_trans
    assumption
    assumption
  ```
  In this example, `targetTypeNumArgs = 1` because `LE` for functions is defined as
  ```
  instance {α : Type u} {β : Type v} [LE β] : LE (α → β) where
    le f g := ∀ i, f i ≤ g i
  ```
  -/
  let rangeNumArgs ← if hasMVarHead then
    pure [numArgs : numArgs+1]
  else
    let targetTypeNumArgs ← getExpectedNumArgs targetType
    pure [numArgs - targetTypeNumArgs : numArgs+1]
  /-
  Auxiliary function for trying to add `n` underscores where `n ∈ [i: rangeNumArgs.stop)`
  See comment above
  -/
  let rec go (i : Nat) : MetaM (Array Expr × Array BinderInfo) := do
    if i < rangeNumArgs.stop then
      let s ← saveState
      let (newMVars, binderInfos, eType) ← forallMetaTelescopeReducing eType i
      if (← isDefEqApply cfg eType targetType) then
        return (newMVars, binderInfos)
      else
        s.restore
        go (i+1)
    else
      let (_, _, eType) ← forallMetaTelescopeReducing eType (some rangeNumArgs.start)
      throwError "apply error: {mvarId} {eType} {targetType}"
    termination_by rangeNumArgs.stop - i
  let (newMVars, binderInfos) ← go rangeNumArgs.start
  postprocessAppMVars `apply mvarId newMVars binderInfos cfg.synthAssignedInstances cfg.allowSynthFailures
  let e ← instantiateMVars e
  mvarId.assign (mkAppN e newMVars)
  let newMVars ← newMVars.filterM fun mvar => not <$> mvar.mvarId!.isAssigned
  let otherMVarIds ← getMVarsNoDelayed e
  let newMVarIds ← reorderGoals newMVars cfg.newGoals
  let otherMVarIds := otherMVarIds.filter fun mvarId => !newMVarIds.contains mvarId
  let result := newMVarIds ++ otherMVarIds.toList
  result.forM (·.headBetaType)
  return result

def extMatch (T : Expr) (ts : (List Expr)) (localMarker : Name) (lems : List Name) (dbg := false) : RecMO U (Option (Expr × List Expr)) := do

  if (← readThe Context).fuel == 0 then
    return none
  -- options := options.insert `trace.Meta.isDefEq (.ofBool true)
  -- let localDfEqs := (← readThe Context).localDfEqs
  -- if dbg then 
  --   dbg_trace s!"DBG[387]: TypeChecker.lean:406 (after if dbg then)"

  let ret? ← (do
    let mut localLems := []
    for decl in (← getLCtx) do
      if dbg then 
        dbg_trace s!"Checking: {decl.userName} : {← ppExpr decl.type}"
      if let .app (.const n []) _ := decl.type.getForallBody then -- TODO remove once we can generate lemmas for intermediate reducts
        if n == localMarker then
          let newType ← liftM $ forallTelescope decl.type fun vs b => mkForallFVars vs b.appArg!
          localLems := localLems ++ [(decl.toExpr, .some newType)]
          if dbg then 
            dbg_trace s!"Added: {decl.userName} : {← ppExpr decl.type}"

    let mut candidates := (← lems.mapM (mkConstWithFreshMVarLevels ·)).zip (List.replicate lems.length none)
    candidates := candidates ++ localLems
    let tryExtEq {U} lem type? (T : Expr) (ts : List Expr) : RecMO U (Option (Expr × List Expr)) := do
      let condString := do pure s!"{← ppExpr $ ← T.mvarId!.getType}"
      -- let dbg := (← readThe Core.Context).options.get? `trace.Kernel.ext
      trace[Kernel.ext] "Trying to show {← condString}"
      try
        trace[Kernel.ext] s!"Trying to apply (fuel {(← read).fuel}): {← ppExpr $ lem} : {← ppExpr $ (← Meta.inferType lem)} to {← condString}"
        let gs ← apply T.mvarId! lem type?

        trace[Kernel.ext] s!"Applying OK:{← ppExpr $ (← Meta.inferType lem)} to  {← condString}" --"\n  {← gs.mapM (fun (id : MVarId) => do ppExpr $ ← id.getType)}\n  {← localLems.mapM (do ppExpr $ ← Meta.inferType ·.1)}"
        if dbg then
          dbg_trace s!"Applying OK:{← ppExpr $ (← Meta.inferType lem)} to  {← condString}" --"\n  {← gs.mapM (do ppExpr $ ← ·.getType)}\n  {← localLems.mapM (do ppExpr $ ← Meta.inferType ·.1)}"
        for g in gs do
          -- TODO unassign T if any g.refl fails?
          try
            trace[Kernel.ext] s!"Trying reflection: {← ppExpr $ ← g.getType}"
            g.refl
            trace[Kernel.ext] s!"Reflection OK: {← ppExpr $ ← g.getType}"
          catch e =>
            trace[Kernel.ext] s!"Reflection FAIL: {← ppExpr $ ← g.getType}"
            throw e
        trace[Kernel.ext] s!"Showing OK: {← ppExpr $ ← T.mvarId!.getType}"
        let TInst ← instantiateMVars T
        let tsInst ← ts.mapM (fun t => instantiateMVars t)
        return some (TInst, tsInst)
      catch e =>
        trace[Kernel.ext] s!"Applying FAIL: {← ppExpr $ lem} : {← ppExpr $ (← Meta.inferType lem)} to {← condString}"
        if dbg then
          dbg_trace s!"Applying FAIL: {← ppExpr $ lem} : {← ppExpr $ (← Meta.inferType lem)} to {← condString}"
        pure none

    for (lem, type?) in candidates do
      -- for eqMvar in [tEqsMvar, sEqtMvar] do
      -- TODO is there a way to "undo" assignments from previous failed unification attempts,
      -- rather than making new mvars every time?
      if let .some prf ← tryExtEq lem type? T ts then
        printTraces
        return some prf
    trace[Kernel.ext] "Showing FAIL: {← ppExpr $ ← T.mvarId!.getType}"
    printTraces
    return none
    )

  if let some (prf, ts) := ret? then
    if prf.hasExprMVar then
      throwError "unexpected mvar found in extensional equality proof"
    if ts.any (·.hasExprMVar) then
       throwError "unexpected mvar found in extensionally assigned variable"
    -- check that the proof returned by unification is well-typed with the kernel itself,
    -- to minimize the trust that we place on unification
    _ ← inferType prf (inferOnly := false)
    return some (prf, ts)

  return none

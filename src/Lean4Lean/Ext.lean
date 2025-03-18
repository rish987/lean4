import Lean4Lean.RecM

namespace Lean.TypeChecker.Inner

def toKernelException (m : EIO Exception α) : EIO KernelException (Sum α Exception) := fun x =>
  match m x with
  | .ok s I => .ok (.inl s) I
  | .error e I => .ok (.inr e) I


def runMetaM (m : MetaM T) : RecM T := do
  let mut options := (← readThe Context).options
  let m' := Lean.Meta.MetaM.run m {lctx := (← readThe Context).lctx, fuel := (← readThe Context).fuel - 1} |>.run {options := options, fileName := default, fileMap := default, maxHeartbeats := 0} {env := (← readThe Context).env'}
  match ← toKernelException m' with
  | .inl ((reqs, _), _) => pure reqs
  | .inr (.internal _ _) => throw $ .other "untranslated Exception.Internal"
  | .inr (.error _ d) => throw $ .other (← d.toString)


open Lean.Meta in
def extMatch (getT : MetaM (Expr × List Expr)) (localMarker : Name) (lems : List Name) (dbg := false) : RecMO T (Option (Expr × List Expr)) := do
  if (← readThe Context).fuel == 0 then
    return none
  -- options := options.insert `trace.Meta.isDefEq (.ofBool true)
  -- let localDfEqs := (← readThe Context).localDfEqs
  -- if dbg then 
  --   dbg_trace s!"DBG[387]: TypeChecker.lean:406 (after if dbg then)"

  let ret? ← runMetaM (do
    let mut localLems := []
    for decl in (← getLCtx) do
      if dbg then 
        dbg_trace s!"Checking: {decl.userName} : {← ppExpr decl.type}"
      if let .app (.const n []) _ := decl.type.getForallBody then -- TODO remove once we can generate lemmas for intermediate reducts
        if n == localMarker then
          let newType ← forallTelescope decl.type fun vs b => mkForallFVars vs b.appArg!
          localLems := localLems ++ [(decl.toExpr, .some newType)]
          if dbg then 
            dbg_trace s!"Added: {decl.userName} : {← ppExpr decl.type}"

    let mut candidates := (← lems.mapM (mkConstWithFreshMVarLevels ·)).zip (List.replicate lems.length none)
    candidates := candidates ++ localLems
    withLCtx' (← read).lctx do
      let (T, _) ← getT
      let condString := do pure s!"{← ppExpr $ ← T.mvarId!.getType}"
      -- let dbg := (← readThe Core.Context).options.get? `trace.Kernel.ext
      trace[Kernel.ext] "Trying to show {← condString}"
      let tryExtEq lem type? T ts := do
        try
          trace[Kernel.ext] s!"Trying to apply (fuel {(← read).fuel}): {← ppExpr $ lem} : {← ppExpr $ (← Meta.inferType lem)} to {← condString}"
          let gs ← T.mvarId!.apply lem (cfg := {shallow := true}) type?

          trace[Kernel.ext] s!"Applying OK:{← ppExpr $ (← Meta.inferType lem)} to  {← condString}\n  {← gs.mapM (do ppExpr $ ← ·.getType)}\n  {← localLems.mapM (do ppExpr $ ← Meta.inferType ·.1)}"
          if dbg then
            dbg_trace s!"Applying OK:{← ppExpr $ (← Meta.inferType lem)} to  {← condString}\n  {← gs.mapM (do ppExpr $ ← ·.getType)}\n  {← localLems.mapM (do ppExpr $ ← Meta.inferType ·.1)}"
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
          let tsInst ← ts.mapM fun t => instantiateMVars t
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
        let (T, ts) ← getT
        if let .some prf ← tryExtEq lem type? T ts then
          printTraces
          return some prf
      trace[Kernel.ext] "Showing FAIL: {← ppExpr $ ← T.mvarId!.getType}"
      printTraces
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

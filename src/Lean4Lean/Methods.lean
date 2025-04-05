import Lean4Lean.TypeChecker

namespace Lean.TypeChecker

open Inner
open Lean

def defFuel := 1000

-- structure Methods where
--   isDefEqCore : Nat → Expr → Expr → Level → Expr → MO T Bool
--   whnfCore (e : Expr) (l : Option (Level × Expr) := none) (cheapRec := false) (cheapProj := false) : MO T Expr
--   whnfCoreNoExt (e : Expr) (l : Option (Level × Expr) := none) (cheapRec := false) (cheapProj := false) : MO T Expr
--   whnf (e : Expr) (d : Option (Level × Expr)) : MO T Expr 
--   inferType (e : Expr) (inferOnly : Bool) : MO T Expr

mutual
def fuelWrap (idx : Nat) (fuel : Nat) (d : CallData) : M (CallDataT d) := do
  -- let trace := (← readThe Context).trace
  -- let trace := false
  let trace := true
  match fuel with
    | 0 =>
      -- dbg_trace s!">deep recursion callstack: {(← readThe Context).callStack.map (·.1)}"
      throw .deepRecursion
    | fuel' + 1 =>
      let m : RecM (CallDataT d):=
        match d with
        | .isDefEqCore t s => isDefEqCoreCheckTypes t s
        | .whnfCore e r p => do
          let ret ← whnfCore' e r p
          -- dbg_trace s!"DBG[A]: TypeChecker.lean:440 {← getTrace true}"
          -- _ ← Inner.inferType 51 ret (inferOnly := false) 
          -- dbg_trace s!"DBG[B]: TypeChecker.lean:481 (after _ ← inferTypeCheck p)"
          pure ret
        | .whnfCoreNoExt e r p => do
          let ret ← whnfCoreNoExt' e r p
          -- dbg_trace s!"DBG[A]: TypeChecker.lean:440 {← getTrace true}"
          -- _ ← Inner.inferType 51 ret (inferOnly := false) 
          -- dbg_trace s!"DBG[B]: TypeChecker.lean:481 (after _ ← inferTypeCheck p)"
          pure ret
        | .whnf e ext => whnf' e ext
        | .inferType e o => do
          let l := (← readThe Context).callStack.map fun d => s!"{d.1}"
          let ret ← inferType' e o
          pure ret
        | .extMatch g l m d => extMatch' g l m d
      modify fun s => {s with numCalls := s.numCalls + 1} 
      let s ← get
      let mut printedTrace := false
      let print := false
      -- let print := true
      if print && trace then
        if true then
          printedTrace := true
          -- let l := (← readThe Context).callStack.map fun d => s!"{d.1}/{d.2.1}"
          let mut l := (← readThe Context).callStack.map fun d =>
            let str := if d.1 == 44003 || d.1 == 43003 then s!" : {toString d.2.2}" else ""
            s!"{d.1}{str}"
          -- if l.size > 20 then
          --   l := l[l.size - 20:]
          dbg_trace s!">calltrace {s.numCalls}: {l}, {idx}, {(← readThe Context).callId}"
      try
        let ret ← withCallId s.numCalls do
          if trace then
            withCallData idx s.numCalls d $ m (Methods.withFuel fuel')
          else
            m (Methods.withFuel fuel')
        -- if printedTrace then
        --   dbg_trace s!">end of    {s.numCalls}: {(← readThe Context).callStack.map (·.1)}, {idx}, {(← readThe Context).callId}"
        pure $ ret
      catch e =>
        -- if trace /- && (← readThe Context).callStack.size == defFuel -/ then
        --   dbg_trace s!">calltrace {s.numCalls}: {((← readThe Context).callStack.map (fun x => (x.1, (x.2.1))))}, {idx}"
        throw e

def Methods.withFuel (n : Nat) : Methods := 
  { isDefEqCore := fun i t s => do
      let ret ← (fuelWrap i n $ .isDefEqCore t s)
      pure ret
    whnfCore := fun i e k p => do
      let ret ← (fuelWrap i n $ .whnfCore e k p)
      pure ret
    whnfCoreNoExt := fun i e k p => do
      let ret ← (fuelWrap i n $ .whnfCoreNoExt e k p)
      pure ret
    whnf := fun i e ext => do
      let ret ← (fuelWrap i n $ .whnf e ext)
      pure $ ret
    inferType := fun i e o => do
      let ret ← (fuelWrap i n $ .inferType e o)
      pure $ ret
    extMatch := fun i g l m d => do
      let ret ← (fuelWrap i n $ .extMatch g l m d)
      pure $ ret
  }
end

def RecM.run (x : RecM α) : M α := x (Methods.withFuel 1000)

def check (e : Expr) (lps : List Name) : M Expr :=
  withReader ({ · with lparams := lps }) (inferType 500 e (inferOnly := false)).run

def whnf (e : Expr) : M Expr := (Inner.whnf 501 e).run

def inferType (e : Expr) : M Expr := (Inner.inferType 502 e).run

def isDefEqCheckTypes' (n : Nat) (lps : List Name) (t s : Expr) : M Bool :=
  withReader ({ · with lparams := lps }) (Inner.isDefEqCheckTypes n t s).run

def isDefEqCheckTypes (lps : List Name) (t s : Expr) : M Bool :=
  withReader ({ · with lparams := lps }) (Inner.isDefEqCheckTypes 503 t s).run

def isDefEq (t s : Expr) : M Bool := (Inner.isDefEq 504 t s).run

def isProp (t : Expr) : M Bool := (Inner.isProp t).run

def ensureSort (t : Expr) (s := t) : M Expr := (ensureSortCore t s).run

def ensureForall (t : Expr) (s := t) : M Expr := (ensureForallCore t s).run

def ensureType (e : Expr) : M Expr := do ensureSort (← inferType e) e

@[export lean_kernel_is_def_eq_new]
def isDefEqK (n : Nat) (lps : List Name) (env : Lean.Environment) (lctx : LocalContext) (a b : Expr) (fuel : Nat) (localDfEqs : List Expr) (options : Options) : EIO Kernel.Exception Bool :=
  M.run env.toKernelEnv env (lctx := lctx) (localDfEqs := localDfEqs) (safety := DefinitionSafety.safe) (fuel := fuel) (options := options) do
    TypeChecker.isDefEqCheckTypes' (500 + n) lps a b

@[export lean_kernel_check_new]
def checkK (n : Nat) (lps : List Name) (env : Lean.Environment) (lctx : LocalContext) (t : Expr) (options : Options) : EIO Kernel.Exception Expr :=
  M.run env.toKernelEnv env (lctx := lctx) (safety := DefinitionSafety.safe) (options := options) do
    TypeChecker.check t lps

-- def Methods.withFuel (n : Nat) : Methods := 
--   { isDefEqCore := fun i t s => do
--       fuelWrap i n $ .isDefEqCore t s
--     whnfCore := fun i e k p => do
--       fuelWrap i n $ .whnfCore e k p
--     whnf := fun i e => do
--       fuelWrap i n $ .whnf e
--     inferType := fun i e d => do
--       fuelWrap i n $ .inferType e d
--   }
-- end
--
-- def RecM.run (x : RecM α) (fuel := defFuel) : M α := x (Methods.withFuel fuel)
--
-- def check (e : Expr) (lps : List Name) : M Expr :=
--   withReader ({ · with lparams := lps }) (inferType 48 e (inferOnly := false)).run
--
-- def whnf (e : Expr) : M Expr := (Inner.whnf 49 e).run
--
-- def inferType (e : Expr) : M Expr := (Inner.inferType 50 e).run
--
-- def inferTypeCheck (e : Expr) : M Expr := (Inner.inferType 51 e (inferOnly := false)).run
--
-- def isDefEq (t s : Expr) (fuel := defFuel) : M Bool := (Inner.isDefEq 69 t s).run fuel
--
-- def isDefEqCore (t s : Expr) : M Bool := (Inner.isDefEqCore 52 t s).run
--
-- def isProp (t : Expr) : M Bool := (Inner.isProp t).run
--
-- def ensureSort (t : Expr) (s := t) : M Expr := (ensureSortCore t s).run
--
-- def ensureForall (t : Expr) (s := t) : M Expr := (ensureForallCore t s).run
--
-- def ensureType (e : Expr) : M Expr := do ensureSort (← inferType e) e

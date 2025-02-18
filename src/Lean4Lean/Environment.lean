import Lean4Lean.TypeChecker
import Lean4Lean.Quot
import Lean4Lean.Inductive.Add
import Lean4Lean.Primitive
import Lean.Compiler

namespace Lean
namespace Environment
open TypeChecker

open private add updateBaseAfterKernelAdd from Lean.Environment

def checkConstantVal (env : Environment) (v : ConstantVal) (allowPrimitive := false) : M Unit := do
  checkName env v.name allowPrimitive
  checkDuplicatedUnivParams v.levelParams
  checkNoMVarNoFVar env v.name v.type
  let sort ← check v.type v.levelParams
  _ ← ensureSort sort v.type

def addAxiom (env : Environment) (v : AxiomVal) (check := true) :
    Except KernelException Environment := do
  if check then
    _ ← (checkConstantVal env v.toConstantVal).run env
      (safety := if v.isUnsafe then .unsafe else .safe)
  return updateBaseAfterKernelAdd env (add env.toKernelEnv (.axiomInfo v))

def addDefinition (env : Environment) (v : DefinitionVal) (check := true) :
    Except KernelException Environment := do
  if let .unsafe := v.safety then
    -- Meta definition can be recursive.
    -- So, we check the header, add, and then type check the body.
    if check then
      _ ← (checkConstantVal env v.toConstantVal).run env (safety := .unsafe)
    let env' := add env (.defnInfo v)
    if check then
      checkNoMVarNoFVar env' v.name v.value
      M.run env' (safety := .unsafe) (lctx := {}) do
        let valType ← TypeChecker.check v.value v.levelParams
        if !(← isDefEq valType v.type) then
          throw <| .declTypeMismatch env' (.defnDecl v) valType
    return env'
  else
    if check then
      M.run env (safety := .safe) (lctx := {}) do
        checkConstantVal env v.toConstantVal (← checkPrimitiveDef env v)
        checkNoMVarNoFVar env v.name v.value
        let valType ← TypeChecker.check v.value v.levelParams
        if !(← isDefEq valType v.type) then
          throw <| .declTypeMismatch env (.defnDecl v) valType
    return add env (.defnInfo v)

def addTheorem (env : Environment) (v : TheoremVal) (check := true) :
    Except KernelException Environment := do
  if check then
    -- TODO(Leo): we must add support for handling tasks here
    M.run env (safety := .safe) (lctx := {}) do
      if !(← isProp v.type) then
        throw <| .thmTypeIsNotProp env v.name v.type
      checkConstantVal env v.toConstantVal
      checkNoMVarNoFVar env v.name v.value
      let valType ← TypeChecker.check v.value v.levelParams
      if !(← isDefEq valType v.type) then
        throw <| .declTypeMismatch env (.thmDecl v) valType
  return add env (.thmInfo v)

def addOpaque (env : Environment) (v : OpaqueVal) (check := true) :
    Except KernelException Environment := do
  if check then
    M.run env (safety := .safe) (lctx := {}) do
      checkConstantVal env v.toConstantVal
      let valType ← TypeChecker.check v.value v.levelParams
      if !(← isDefEq valType v.type) then
        throw <| .declTypeMismatch env (.opaqueDecl v) valType
  return add env (.opaqueInfo v)

def addMutual (env : Environment) (vs : List DefinitionVal) (check := true) :
    Except KernelException Environment := do
  let v₀ :: _ := vs | throw <| .other "invalid empty mutual definition"
  if let .safe := v₀.safety then
    throw <| .other "invalid mutual definition, declaration is not tagged as unsafe/partial"
  if check then
    M.run env (safety := v₀.safety) (lctx := {}) do
      for v in vs do
        if v.safety != v₀.safety then
          throw <| .other
            "invalid mutual definition, declarations must have the same safety annotation"
        checkConstantVal env v.toConstantVal
  let mut env' := env
  for v in vs do
    env' := add env' (.defnInfo v)
  if check then
    M.run env' (safety := v₀.safety) (lctx := {}) do
      for v in vs do
        checkNoMVarNoFVar env' v.name v.value
        let valType ← TypeChecker.check v.value v.levelParams
        if !(← isDefEq valType v.type) then
          throw <| .declTypeMismatch env' (.mutualDefnDecl vs) valType
  return env'

/-- Type check given declaration and add it to the environment -/
@[export lean_add_decl_new]
def addDecl' (env : Environment) (decl : Declaration) (check := true) :
    Except KernelException Environment := do
  match decl with
  | .axiomDecl v =>
    dbg_trace s!"DBG[14]: Environment.lean:104 (after | .axiomDecl v =>)"
    addAxiom env v check
  | .defnDecl v =>
    dbg_trace s!"DBG[13]: Environment.lean:106 {v.name}"
    addDefinition env v check
  | .thmDecl v =>
    dbg_trace s!"DBG[12]: Environment.lean:108 {v.name} {Lean.isNoncomputable env v.name}"
    let ret ← addTheorem env v check
    dbg_trace s!"DBG[16]: Environment.lean:112 (after let ret ← addTheorem env v check)"
    pure ret
  | .opaqueDecl v =>
    dbg_trace s!"DBG[11]: Environment.lean:110 (after | .opaqueDecl v =>)"
    addOpaque env v check
  | .mutualDefnDecl v =>
    dbg_trace s!"DBG[10]: Environment.lean:112 (after | .mutualDefnDecl v =>)"
    addMutual env v check
  | .quotDecl =>
    dbg_trace s!"DBG[9]: Environment.lean:114 (after | .quotDecl =>)"
    addQuot env
  | .inductDecl lparams nparams types isUnsafe =>
    dbg_trace s!"DBG[17]: Environment.lean:124 (after | .inductDecl lparams nparams types isUn…)"
    let allowPrimitive ← checkPrimitiveInductive env lparams nparams types isUnsafe
    let ret ← addInductive env lparams nparams types isUnsafe allowPrimitive
    dbg_trace s!"DBG[18]: Environment.lean:127 (after addInductive env lparams nparams types i…)"
    pure ret

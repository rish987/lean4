import Lean4Lean.TypeChecker
import Lean4Lean.Quot
import Lean4Lean.Inductive.Add
import Lean4Lean.Primitive

namespace Lean
namespace Kernel.Environment
open Lean.TypeChecker

open private add from Lean.Environment

def checkConstantVal (env : Kernel.Environment) (v : ConstantVal) (allowPrimitive := false) : M Unit := do
  checkName env v.name allowPrimitive
  checkDuplicatedUnivParams v.levelParams
  checkNoMVarNoFVar env v.name v.type
  let sort ← TypeChecker.check v.type v.levelParams
  _ ← ensureSort sort v.type

variable (env' : Lean.Environment)

def addAxiom (env : Kernel.Environment) (v : AxiomVal) (check := true) :
    EIO KernelException Kernel.Environment := do
  if check then
    _ ← (checkConstantVal env v.toConstantVal).run env env'
      (safety := if v.isUnsafe then .unsafe else .safe)
  return (add env (.axiomInfo v))

def addDefinition (env : Kernel.Environment) (v : DefinitionVal) (check := true) :
    EIO KernelException Kernel.Environment := do
  if let .unsafe := v.safety then
    -- Meta definition can be recursive.
    -- So, we check the header, add, and then type check the body.
    if check then
      _ ← (checkConstantVal env v.toConstantVal).run env env' (safety := .unsafe)
    let newEnv := add env (.defnInfo v)
    if check then
      checkNoMVarNoFVar newEnv v.name v.value
      M.run newEnv env' (safety := .unsafe) (lctx := {}) do
        let valType ← TypeChecker.check v.value v.levelParams
        if !(← TypeChecker.isDefEqCheckTypes valType v.type) then
          throw <| .declTypeMismatch newEnv (.defnDecl v) valType
    return newEnv
  else
    if check then
      M.run env env' (safety := .safe) (lctx := {}) do
        checkConstantVal env v.toConstantVal (← checkPrimitiveDef env v)
        checkNoMVarNoFVar env v.name v.value
        let valType ← TypeChecker.check v.value v.levelParams
        if !(← TypeChecker.isDefEqCheckTypes valType v.type) then
          throw <| .declTypeMismatch env (.defnDecl v) valType
    return add env (.defnInfo v)

def addTheorem (env : Kernel.Environment) (v : TheoremVal) (check := true) :
    EIO KernelException Kernel.Environment := do
  if check then
    -- TODO(Leo): we must add support for handling tasks here
    M.run env env' (safety := .safe) (lctx := {}) do
      if !(← isProp v.type) then
        throw <| .thmTypeIsNotProp env v.name v.type
      checkConstantVal env v.toConstantVal
      checkNoMVarNoFVar env v.name v.value
      let valType ← TypeChecker.check v.value v.levelParams
      if !(← TypeChecker.isDefEqCheckTypes valType v.type) then
        throw <| .declTypeMismatch env (.thmDecl v) valType
  return add env (.thmInfo v)

def addOpaque (env : Kernel.Environment) (v : OpaqueVal) (check := true) :
    EIO KernelException Kernel.Environment := do
  if check then
    M.run env env' (safety := .safe) (lctx := {}) do
      checkConstantVal env v.toConstantVal
      let valType ← TypeChecker.check v.value v.levelParams
      if !(← TypeChecker.isDefEqCheckTypes valType v.type) then
        throw <| .declTypeMismatch env (.opaqueDecl v) valType
  return add env (.opaqueInfo v)

def addMutual (env : Kernel.Environment) (vs : List DefinitionVal) (check := true) :
    EIO KernelException Kernel.Environment := do
  let v₀ :: _ := vs | throw <| .other "invalid empty mutual definition"
  if let .safe := v₀.safety then
    throw <| .other "invalid mutual definition, declaration is not tagged as unsafe/partial"
  if check then
    M.run env env' (safety := v₀.safety) (lctx := {}) do
      for v in vs do
        if v.safety != v₀.safety then
          throw <| .other
            "invalid mutual definition, declarations must have the same safety annotation"
        checkConstantVal env v.toConstantVal
  let mut newEnv := env
  for v in vs do
    newEnv := add newEnv (.defnInfo v)
  if check then
    M.run newEnv env' (safety := v₀.safety) (lctx := {}) do
      for v in vs do
        checkNoMVarNoFVar newEnv v.name v.value
        let valType ← TypeChecker.check v.value v.levelParams
        if !(← TypeChecker.isDefEqCheckTypes valType v.type) then
          throw <| .declTypeMismatch newEnv (.mutualDefnDecl vs) valType
  return newEnv
end Kernel.Environment

namespace Environment

open private updateBaseAfterKernelAdd from Lean.Environment

/-- Type check given declaration and add it to the environment -/
@[export lean_add_decl_new]
def addDecl' (env' : Environment) (decl : Declaration) (check := true) :
    EIO KernelException Environment := do
  let env := env'.toKernelEnv
  let newEnv ← match decl with
  | .axiomDecl v =>
    env.addAxiom env' v check
  | .defnDecl v =>
    env.addDefinition env' v check
  | .thmDecl v =>
    env.addTheorem env' v check
  | .opaqueDecl v =>
    env.addOpaque env' v check
  | .mutualDefnDecl v =>
    env.addMutual env' v check
  | .quotDecl =>
    env.addQuot
  | .inductDecl lparams nparams types isUnsafe =>
    let allowPrimitive ← env.checkPrimitiveInductive env' lparams nparams types isUnsafe
    env.addInductive env' lparams nparams types isUnsafe allowPrimitive
  return updateBaseAfterKernelAdd env' newEnv

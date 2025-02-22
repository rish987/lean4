/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
prelude
import Lean.Meta.InferType
import Lean.AuxRecursor
import Lean.Structure
import Lean.Meta.CompletionName

open Lean Meta

def mkStructEta (n : Name) : MetaM Unit := do
  let .inductInfo indVal ← getConstInfo n | unreachable!
  if not (isStructureLike (← getEnv) n) then return
  let .ctorInfo ctorInfo ← getConstInfo indVal.ctors[0]! | unreachable!

  let decl ← forallTelescope ctorInfo.type fun xs t => do
    let params := xs[:indVal.numParams]
    -- let e := .const recInfo.name (recInfo.levelParams.map (.param ·))
    let T := mkAppN (.const indVal.name (indVal.levelParams.map mkLevelParam)) params
    withLocalDecl `s BinderInfo.implicit T fun s =>
    withLocalDecl `s' BinderInfo.implicit T fun s' => do
    let numProj := ctorInfo.numFields
    let mut hypTypes := #[]
    for projIdx in [:numProj] do
      let type := Lean.mkAppN (Expr.const `Eq sorry) #[.proj indVal.name projIdx s]
      hypTypes := hypTypes.push hyp
    -- We reorder the parameters
    -- before: As Cs minor_premises indices major-premise
    -- fow:    As Cs indices major-premise minor-premises
    let vs :=
      params ++
      xs[AC_size + recInfo.numMinors:AC_size + recInfo.numMinors + 1 + recInfo.numIndices] ++
      xs[AC_size:AC_size + recInfo.numMinors]
    let type ← mkForallFVars vs t
    let value ← mkLambdaFVars vs e
    mkDefinitionValInferrringUnsafe (mkRecOnName n) recInfo.levelParams type value .abbrev

  addDecl (.defnDecl decl)
  setReducibleAttribute decl.name
  modifyEnv fun env => markAuxRecursor env decl.name
  modifyEnv fun env => addProtected env decl.name

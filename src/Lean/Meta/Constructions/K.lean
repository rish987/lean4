/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
prelude
import Lean.Meta.InferType
import Lean.AuxRecursor
import Lean.AddDecl
import Lean.Meta.CompletionName

open Lean Meta

def mkK (n : Name) : MetaM Unit := do
  let .recInfo recInfo ← getConstInfo (mkRecName n)
    | throwError "{mkRecName n} not a recinfo"
  if not recInfo.k then return
  let .inductInfo inductInfo ← getConstInfo n
    | throwError "{n} not an inductive type"
  let [ctor] := inductInfo.ctors | unreachable!
  let .ctorInfo ctorInfo ← getConstInfo ctor
    | throwError "{ctor} not a constructor"
  let decl ← forallTelescope ctorInfo.type fun args uniqType => do
    withLocalDeclD default uniqType fun major => do
      let ctorApp := Lean.mkAppN (.const ctorInfo.name (ctorInfo.levelParams.map mkLevelParam)) args
      let eq := Lean.mkAppN (.const ``Eq [0]) #[uniqType, major, ctorApp]
      dbg_trace s!"DBG[252]: K.lean:26: eq={eq}"
      let args := args ++ [major]
      let type ← mkForallFVars args eq
      -- mkDefinitionValInferrringUnsafe (mkRecOnName n) recInfo.levelParams type value .abbrev
      let name := Name.str n "_k"

      dbg_trace s!"DBG[251]: K.lean:30: name={name}"
      return { name, levelParams := ctorInfo.levelParams, type, isUnsafe := false }
  addDecl (.axiomDecl decl)

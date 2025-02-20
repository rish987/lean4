/-
Copyright (c) 2022 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen, Thomas Murrills, Joachim Breitner
-/
prelude
import Lean.Meta.Tactic.Apply
import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Refl

/-!
# `rfl` tactic extension for reflexive relations

This extends the `rfl` tactic so that it works on any reflexive relation,
provided the reflexivity lemma has been marked as `@[refl]`.
-/

namespace Lean.Meta.DfEq

open Lean Meta

-- /-- Environment extensions for `refl` lemmas -/
initialize dfEqExt :
    SimpleScopedEnvExtension Name (List Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt n => dt.insert n
    initial := {}
  }

builtin_initialize registerBuiltinAttribute {
  name := `dfeq
  descr := "definitional equality"
  add := fun decl _ kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let (_, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
    let fail := throwError
      "@[dfeq] attribute only applies to lemmas proving x = x, got {declTy}"
    let .app (.app rel lhs) rhs := targetTy | fail
    let .app (.const ``Eq [_]) _ := rel | fail
    -- unless ← withNewMCtxDepth <| isDefEq lhs rhs do fail
    dfEqExt.add decl kind
}

end Lean.Meta.DfEq

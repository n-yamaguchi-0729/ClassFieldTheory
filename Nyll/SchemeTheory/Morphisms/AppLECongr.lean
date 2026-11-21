/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Restricted sections of equal scheme morphisms

Equality of scheme morphisms identifies their maps on the same source and target opens.
The schemes share the universe required by their category; no field or curve assumption is used.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- Equal scheme morphisms induce the same restricted section map, for either inclusion proof. -/
theorem appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

/-- Every source open lies in the inverse image of the whole target. -/
theorem le_preimage_top {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) :
    U ≤ f ⁻¹ᵁ ⊤ :=
  (le_top : U ≤ ⊤).trans f.preimage_top.ge

/-- Restricting a scheme morphism from the top open to the top open gives its
usual map on global sections. -/
theorem appLE_top_eq_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f.appLE ⊤ ⊤ (le_preimage_top f ⊤) = f.appTop :=
  f.appLE_eq_app

end AlgebraicGeometry.Scheme.Hom

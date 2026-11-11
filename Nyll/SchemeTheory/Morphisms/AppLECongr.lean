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

end AlgebraicGeometry.Scheme.Hom

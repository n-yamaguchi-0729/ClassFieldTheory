/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations

/-!
# Cotangent vanishing under composition

The localness of every stalk map preserves maximal ideals. A morphism sending
maximal ideals into their squares therefore retains this property after
postcomposition by any scheme morphism.
-/

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism with zero cotangent map retains that property after postcomposition. -/
theorem map_maximalIdeal_le_sq_comp
    (hf : ∀ x : X, (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map
      (f.stalkMap x).hom ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2) (x : X) :
    (IsLocalRing.maximalIdeal (Z.presheaf.stalk ((f ≫ g) x))).map
      ((f ≫ g).stalkMap x).hom ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2 := by
  rw [stalkMap_comp]
  change (IsLocalRing.maximalIdeal _).map
    ((f.stalkMap x).hom.comp (g.stalkMap (f x)).hom) ≤ _
  rw [← Ideal.map_map]
  exact (Ideal.map_mono (IsLocalRing.map_maximalIdeal_le _)).trans (hf x)

end AlgebraicGeometry.Scheme.Hom

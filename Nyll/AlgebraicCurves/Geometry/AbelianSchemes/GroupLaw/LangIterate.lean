/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.LangPointFormula
import Nyll.SchemeTheory.Morphisms.StalkIdealPower

/-!
# Lang maps of positive iterates

A positive iterate of a morphism with zero cotangent map still has zero
cotangent map. The geometric Lang theorem consequently applies to every
positive iterate, without imposing a restriction on the characteristic.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

universe u

variable {K : Type u} [Field K] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of K)} (π : SchemeHomOver f f)
    (hdπ : ∀ x : A,
      (IsLocalRing.maximalIdeal (A.presheaf.stalk (π.val x))).map (π.val.stalkMap x).hom ≤
        IsLocalRing.maximalIdeal (A.presheaf.stalk x) ^ 2)

include hdπ

/-- Every positive iterate has zero cotangent map when the original morphism does. -/
theorem map_maximalIdeal_le_sq_npow (n : ℕ) (hn : n ≠ 0) (x : A) :
    (IsLocalRing.maximalIdeal (A.presheaf.stalk ((schemeHomOverNpow π n).val x))).map
      ((schemeHomOverNpow π n).val.stalkMap x).hom ≤
        IsLocalRing.maximalIdeal (A.presheaf.stalk x) ^ 2 := by
  induction n generalizing x with
  | zero => exact (hn rfl).elim
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      have he : schemeHomOverNpow π 1 = π := NeronModelInfra.schemeHomOverComp_id_left π
      exact he.symm ▸ hdπ x
    · exact Scheme.Hom.map_maximalIdeal_le_sq_comp (schemeHomOverNpow π n).val π.val
        (fun y => ih hn0 y) x

/-- Lang's geometric surjection applies to every positive iterate. -/
theorem surjective_langMap_npow_points [IsAlgClosed K]
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f) (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (fun x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f =>
      NeronModelInfra.schemeHomOverComp x (L.langMap hc (schemeHomOverNpow π n))) :=
  L.surjective_langMap_points_of_map_maximalIdeal_le_sq hc hA (schemeHomOverNpow π n)
    (map_maximalIdeal_le_sq_npow π hdπ n hn)

end GoodReductionJacobian.RelativeGroupLaw

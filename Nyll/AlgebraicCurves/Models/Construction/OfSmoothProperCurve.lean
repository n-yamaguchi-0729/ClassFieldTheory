/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_iso_pullback_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Construction.Basic
import Nyll.AlgebraicCurves.Places.ValuationRings.RangeStalkEq
import Nyll.AlgebraicCurves.Models.LocalGeometry.EqRangeStalkEq
import Nyll.AlgebraicCurves.Models.LocalGeometry.ClosedPointRangeStalkEq
import Nyll.AlgebraicCurves.Models.Charts.IsAffineOpenMemFinsetField

/-!
# The actual curve model of a smooth proper integral curve

Construct the model on the given scheme and its actual function field.
In particular, the structure map is definitionally the given map, so iterated
constant base changes can use the same scheme and field embeddings.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicCurve.CurveModel

/-- The place model on the original smooth proper curve and its actual function field. -/
def ofSmoothProperCurve {k : Type u} [Field k] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of k)) [IsIntegral C] [IsProper c]
    [SmoothOfRelativeDimension 1 c] :
    let _ : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
    CurveModel k C.functionField := by
  intro alg
  classical
  have hplace : ∀ x : closedPoints C, ∃ v : Place k C.functionField,
      (algebraMap (C.presheaf.stalk x.1) C.functionField).range =
        v.toValuationSubring.toSubring :=
    fun x => exists_place_range_stalk_eq c x.1 (mem_closedPoints_iff.mp x.2)
  choose pl hpl using hplace
  have hinj : Function.Injective pl := fun x y hxy =>
    Subtype.ext (eq_of_range_stalk_eq c x.1 y.1 (by rw [hpl x, hpl y, hxy]))
  have hsurj : Function.Surjective pl := fun v => by
    obtain ⟨x, hxc, hx⟩ := exists_closedPoint_range_stalk_eq c v
    refine ⟨⟨x, mem_closedPoints_iff.mpr hxc⟩, Place.ext ?_⟩
    apply ValuationSubring.toSubring_injective
    rw [← hpl, hx]
  exact
    { C := C
      toBase := c
      ffEquiv := RingEquiv.refl _
      ffEquiv_algebraMap := fun _ => rfl
      placeOfPoint := pl
      placeOfPoint_bijective := ⟨hinj, hsurj⟩
      range_stalk_eq := fun x => by rw [← hpl x]; rfl
      finset_subset_affineOpen := exists_isAffineOpen_forall_mem_of_finset_of_field c }

end AlgebraicCurve.CurveModel

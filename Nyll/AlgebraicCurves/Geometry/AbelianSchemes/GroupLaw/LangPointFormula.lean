/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.LangMap

/-!
# The Lang map on actual points

Polynomial evaluation at `X - 1` is the pointwise quotient of the image by the
original point. These formulas connect the geometric Lang map to coboundaries.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

universe u

variable {K : Type u} [Field K] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of K)} (L : RelativeGroupLaw K f)
    (hc : L.IsCommutative) (π : SchemeHomOver f f)

/-- The polynomial Lang map is the quotient of the endomorphism by the identity point. -/
theorem langMap_eq_mul_inv :
    L.langMap hc π = L.mul f π (L.inv f (schemeHomOverId f)) := by
  let : CommGroup (SchemeHomOver f f) := L.pointCommGroup hc f
  unfold langMap endAeval
  rw [show (Polynomial.X - 1 : Polynomial ℤ).natDegree = 1 by
    simpa only [Polynomial.C_1] using Polynomial.natDegree_X_sub_C (1 : ℤ)]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, Polynomial.coeff_sub,
    Polynomial.coeff_X_zero, zero_sub,
    Polynomial.coeff_X_one, Polynomial.coeff_one, ite_eq_right (Nat.one_ne_zero), ite_true,
    sub_zero,
    zpow_neg_one, zpow_one, _root_.one_mul, schemeHomOverNpow_succ,
    schemeHomOverNpow_zero, schemeHomOverComp_id_left]
  exact _root_.mul_comm ((schemeHomOverId f)⁻¹) π

/-- Precomposition evaluates the Lang map as the actual pointwise quotient. -/
theorem comp_langMap {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (x : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp x (L.langMap hc π) =
      L.mul t (NeronModelInfra.schemeHomOverComp x π) (L.inv t x) := by
  let : CommGroup (SchemeHomOver f f) := L.pointCommGroup hc f
  let : CommGroup (SchemeHomOver t f) := L.pointCommGroup hc t
  let c : SchemeHomOver f f →* SchemeHomOver t f :=
    { toFun := NeronModelInfra.schemeHomOverComp x
      map_one' := L.one_natural f t x.val x.property
      map_mul' := L.mul_natural f t x.val x.property }
  change c (L.langMap hc π) = c π * x⁻¹
  rw [langMap_eq_mul_inv]
  change c (π * (schemeHomOverId f)⁻¹) = c π * x⁻¹
  rw [map_mul, map_inv]
  exact congrArg (fun z => c π * z⁻¹) (schemeHomOverComp_id_right x)

end GoodReductionJacobian.RelativeGroupLaw

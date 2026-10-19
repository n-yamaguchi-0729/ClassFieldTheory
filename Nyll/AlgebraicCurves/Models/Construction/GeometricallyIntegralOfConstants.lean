/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Construction.Basic
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Places.Basic
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricallyConnectedProperBijectiveAppTop
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricallyIntegralSmooth

/-!
# Geometric integrality of a curve model over its full constants

Regular global functions belong to the zero Riemann--Roch space. When constants
are the base field, the structure map induces an isomorphism on global functions.
Properness and smoothness then give geometric connectedness and integrality.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicCurve.CurveModel

variable {k F : Type} [Field k] [Field F] [Algebra k F] (M : CurveModel k F)

/-- Every global function on the model is constant when the function field has full constants. -/
theorem bijective_appTop_of_constantsAreBase (hC : ConstantsAreBase k F) :
    Function.Bijective M.toBase.appTop := by
  let j : Γ(M.C, ⊤) →+* F := M.ffEquiv.symm.toRingHom.comp
    (M.C.presheaf.germ ⊤ (genericPoint M.C) (TopologicalSpace.Opens.mem_top _)).hom
  have hj : Function.Injective j := M.ffEquiv.symm.injective.comp
    (germ_injective_of_isIntegral M.C (genericPoint M.C) (TopologicalSpace.Opens.mem_top _))
  have hconst (a : k) : j (M.toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a)) =
      algebraMap k F a := by
    change M.ffEquiv.symm (baseToFunctionField M.toBase a) = _
    rw [← M.ffEquiv_algebraMap, M.ffEquiv.symm_apply_apply]
  have hs (s : Γ(M.C, ⊤)) : j s ∈ LSpace (0 : Divisor k F) := by
    apply mem_lSpace_iff_ord.mpr
    right
    intro v
    obtain ⟨x, rfl⟩ := M.placeOfPoint_bijective.2 v
    have hrange : j s ∈ ((M.ffEquiv.symm : M.C.functionField ≃+* F).toRingHom.comp
        (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField)).range := by
      refine ⟨M.C.presheaf.germ ⊤ x.1 (TopologicalSpace.Opens.mem_top _) s, ?_⟩
      change M.ffEquiv.symm ((M.C.presheaf.stalkSpecializes (genericPoint_specializes x.1)).hom
        (M.C.presheaf.germ ⊤ x.1 (TopologicalSpace.Opens.mem_top _) s)) = j s
      rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
      rfl
    rw [M.range_stalk_eq x] at hrange
    simpa only [Finsupp.coe_zero, Pi.zero_apply, neg_zero] using
      (M.placeOfPoint x).ord_nonneg_of_mem hrange
  have hsurj : Function.Surjective M.toBase.appTop := by
    intro s
    have h := hs s
    rw [hC] at h
    obtain ⟨a, ha⟩ := h
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).inv a, hj ?_⟩
    exact (hconst a).trans ha
  refine ⟨?_, hsurj⟩
  intro a b hab
  let E := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  have hE (t : Γ(Spec (CommRingCat.of k), ⊤)) : E.symm (E t) = t := E.symm_apply_apply t
  apply E.injective
  apply (algebraMap k F).injective
  rw [← hconst, ← hconst]
  change j (M.toBase.appTop (E.symm (E a))) = j (M.toBase.appTop (E.symm (E b)))
  rw [hE, hE, hab]

/-- A proper smooth curve model over its full constant field is geometrically integral. -/
theorem geometricallyIntegral_of_constantsAreBase (hC : ConstantsAreBase k F) :
    GeometricallyIntegral M.toBase := by
  have hsm : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have hconn : GeometricallyConnected M.toBase :=
    geometricallyConnected_of_isProper_of_bijective_appTop M.toBase
      (M.bijective_appTop_of_constantsAreBase hC)
  exact geometricallyIntegral_of_smooth_of_geometricallyConnected M.toBase

end AlgebraicCurve.CurveModel

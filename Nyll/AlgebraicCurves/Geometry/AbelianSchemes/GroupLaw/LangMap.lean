/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawEtaleEndKerStrEndAeval
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawEtaleSchemeNsmul
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawSmoothOfRelativeDimension

/-!
# Lang maps on smooth proper connected commutative groups

If a self-map has zero cotangent map, every polynomial in it whose constant coefficient
is nonzero in the ground field is étale and surjective. In particular, subtracting the
identity gives a surjective map on geometric points. The constant coefficient of `X - 1`
is a unit in every characteristic, including the characteristic of the ground field.

This supplies the geometric step of Lang's argument. The hypothesis is an explicit
condition on the stalk maps of the actual scheme morphism; identifying it for a
Frobenius morphism and identifying geometric points with a Picard group are separate steps.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_etale_endKerStr_endAeval_of_map_maximalIdeal_le_sq.P2mFrobSep
open RelativeGroupLaw_etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension.R1NeronObjE4

namespace GoodReductionJacobian.RelativeGroupLaw

variable {K : Type u} [Field K] [IsAlgClosed K]
  {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
  (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
  (hA : AbelianSchemePropertyBundle K f) (π : SchemeHomOver f f)

include hA in
/-- Polynomial self-maps with invertible constant coefficient are étale when the
endomorphism has zero cotangent map. -/
theorem etale_endAeval_of_map_maximalIdeal_le_sq
    (hdπ : ∀ x : A,
      (IsLocalRing.maximalIdeal (A.presheaf.stalk (π.1.base x))).map (π.1.stalkMap x).hom ≤
        IsLocalRing.maximalIdeal (A.presheaf.stalk x) ^ 2)
    (P : Polynomial ℤ) (hP : ((P.coeff 0 : ℤ) : K) ≠ 0) :
    Etale (L.endAeval hc π P).1 := by
  have : Smooth f := hA.smooth
  obtain ⟨d, hd⟩ := L.exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
  have hd' : SmoothOfRelativeDimension d ((L.endAeval hc π P).1 ≫ f) := by
    rw [(L.endAeval hc π P).2]
    exact hd
  have hu : FormallyUnramified (L.endAeval hc π P).1 :=
    formallyUnramified_endAeval f L hc π hdπ P hP
  exact scheme_etale_of_formallyUnramified_of_smoothOfRelativeDimension d hd' hd hu

include hA in
/-- Properness and connectedness turn the étale polynomial self-map into a surjection. -/
theorem surjective_endAeval_of_map_maximalIdeal_le_sq
    (hdπ : ∀ x : A,
      (IsLocalRing.maximalIdeal (A.presheaf.stalk (π.1.base x))).map (π.1.stalkMap x).hom ≤
        IsLocalRing.maximalIdeal (A.presheaf.stalk x) ^ 2)
    (P : Polynomial ℤ) (hP : ((P.coeff 0 : ℤ) : K) ≠ 0) :
    Surjective (L.endAeval hc π P).1 := by
  have : Etale (L.endAeval hc π P).1 :=
    L.etale_endAeval_of_map_maximalIdeal_le_sq hc hA π hdπ P hP
  have : IsProper f := hA.proper
  have : IsProper ((L.endAeval hc π P).1 ≫ f) := by
    rw [(L.endAeval hc π P).2]
    exact hA.proper
  have : IsProper (L.endAeval hc π P).1 := IsProper.of_comp _ f
  have : ConnectedSpace A := by
    rw [connectedSpace_iff_univ]
    have hconn : _root_.IsConnected (f.base ⁻¹' {IsLocalRing.closedPoint K}) :=
      hA.connectedFibres (IsLocalRing.closedPoint K)
    have hfibre : f.base ⁻¹' {IsLocalRing.closedPoint K} = Set.univ := by
      ext x
      simp only [Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rwa [hfibre] at hconn
  refine ⟨?_⟩
  have hclopen : IsClopen (Set.range (L.endAeval hc π P).1.base) :=
    ⟨(L.endAeval hc π P).1.isClosedMap.isClosed_range,
      (L.endAeval hc π P).1.isOpenMap.isOpen_range⟩
  exact Set.range_eq_univ.mp (hclopen.eq_univ (Set.range_nonempty _))

/-- The Lang map associated to a self-map, expressed using the actual relative group law. -/
def langMap : SchemeHomOver f f := L.endAeval hc π (Polynomial.X - 1)

include hA in
/-- The Lang map is étale in every characteristic when the self-map has zero cotangent map. -/
theorem etale_langMap_of_map_maximalIdeal_le_sq
    (hdπ : ∀ x : A,
      (IsLocalRing.maximalIdeal (A.presheaf.stalk (π.1.base x))).map (π.1.stalkMap x).hom ≤
        IsLocalRing.maximalIdeal (A.presheaf.stalk x) ^ 2) :
    Etale (L.langMap hc π).1 := by
  apply L.etale_endAeval_of_map_maximalIdeal_le_sq hc hA π hdπ
  simpa only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_one_zero,
    zero_sub, Int.cast_neg, Int.cast_one] using (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0))

include hA in
/-- The Lang map is surjective in every characteristic. -/
theorem surjective_langMap_of_map_maximalIdeal_le_sq
    (hdπ : ∀ x : A,
      (IsLocalRing.maximalIdeal (A.presheaf.stalk (π.1.base x))).map (π.1.stalkMap x).hom ≤
        IsLocalRing.maximalIdeal (A.presheaf.stalk x) ^ 2) :
    Surjective (L.langMap hc π).1 := by
  apply L.surjective_endAeval_of_map_maximalIdeal_le_sq hc hA π hdπ
  simpa only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_one_zero,
    zero_sub, Int.cast_neg, Int.cast_one] using (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0))

include hA in
/-- Every geometric point has a preimage under the Lang map. -/
theorem surjective_langMap_points_of_map_maximalIdeal_le_sq
    (hdπ : ∀ x : A,
      (IsLocalRing.maximalIdeal (A.presheaf.stalk (π.1.base x))).map (π.1.stalkMap x).hom ≤
        IsLocalRing.maximalIdeal (A.presheaf.stalk x) ^ 2) :
    Function.Surjective (fun x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f =>
      NeronModelInfra.schemeHomOverComp x (L.langMap hc π)) := by
  let β := L.langMap hc π
  have : Etale β.1 := L.etale_langMap_of_map_maximalIdeal_le_sq hc hA π hdπ
  have : Surjective β.1 := L.surjective_langMap_of_map_maximalIdeal_le_sq hc hA π hdπ
  intro x
  have : JacobsonSpace (pullback (C := Scheme) β.1 x.1) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd β.1 x.1)
  have hne : (Set.univ : Set (pullback (C := Scheme) β.1 x.1)).Nonempty := by
    have hs : Surjective (pullback.snd β.1 x.1) := inferInstance
    obtain ⟨z, -⟩ := hs.surj (IsLocalRing.closedPoint K)
    exact ⟨z, trivial⟩
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints hne isOpen_univ.isLocallyClosed
  let q := pointOfClosedPoint (pullback.snd β.1 x.1) z hz ≫ pullback.fst β.1 x.1
  have hq : q ≫ β.1 = x.1 := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact (congrArg (· ≫ x.1)
      (pointOfClosedPoint_comp (pullback.snd β.1 x.1) z hz)).trans
        (Category.id_comp x.1)
  have hqf : q ≫ f = 𝟙 _ := by
    rw [← β.2, ← Category.assoc, hq]
    exact x.2
  exact ⟨⟨q, hqf⟩, Subtype.ext hq⟩

end GoodReductionJacobian.RelativeGroupLaw

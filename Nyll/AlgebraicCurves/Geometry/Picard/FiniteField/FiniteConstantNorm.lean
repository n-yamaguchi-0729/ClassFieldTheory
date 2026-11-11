/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.ConstantExtension.PicardNormRealization
public import Nyll.AlgebraicCurves.Geometry.Picard.FiniteField.FiniteFieldDegreeOne
public import Nyll.AlgebraicCurves.FunctionFields.Extensions.CurveIffTranscendentalFiniteDimensional
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Basic.Countable.Small

/-!
# Actual Picard norms for finite constant composita

Choose the actual smooth proper model and its geometric base change from the
given function field. The concrete comparison proves the norm criterion for
the supplied finite constant compositum without requiring a curve model as input.
-/

@[expose] public section

universe u v w t

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicCurve.Pic

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {k : Type u} {E : Type v} {K : Type w} {L : Type t}
    [Field k] [Finite k] [Field E] [Finite E] [Field K] [Field L]
    [Algebra k E] [Algebra k K] [Algebra k L] [Algebra E L] [Algebra K L]
    [IsScalarTower k E L] [IsScalarTower k K L]
    [IsCurveOver k K] [Algebra.EssFiniteType k K]
    [FiniteDimensional K L] [IsGalois K L] [HasPrincipalDivisors k L]

/-- Actual norms from a finite constant compositum are exactly the classes of divisible degree. -/
theorem mem_norm_range_iff_of_finite_constants
    (hC : ConstantsAreBase k K)
    (hgen : Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤)
    (hdeg : Module.finrank K L = Module.finrank k E) (x : Pic k K) :
    x ∈ (norm (k := k) (K := K) (L := L)).range ↔
      (Module.finrank k E : ℤ) ∣ H1Gm.degree k K x := by
  obtain ⟨t, ht, hfin, -⟩ :=
    (isCurveOver_iff_exists_transcendental_finiteDimensional (K := k) (F := K)).mp
      (inferInstance : IsCurveOver k K)
  obtain ⟨M₀⟩ := CurveModel.nonempty_of_perfectField k K ⟨t, ht, hfin⟩
  have hgeom : GeometricallyIntegral M₀.toBase := M₀.geometricallyIntegral_of_constantsAreBase hC
  -- Only the finite constants are represented in the scheme category's universe.
  -- The original function fields and their actual Picard norm stay unchanged.
  let E' := Shrink.{u} E
  let eE : E' ≃ₐ[k] E := Shrink.algEquiv.{u,u,v} k E
  let : Finite E' := Finite.of_equiv E eE.symm.toEquiv
  let algE'L : Algebra E' L := ((algebraMap E L).comp eE.toRingHom).toAlgebra
  have towerE'L : IsScalarTower k E' L :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      change algebraMap k L a = algebraMap E L (eE (algebraMap k E' a))
      rw [eE.commutes]
      exact IsScalarTower.algebraMap_apply k E L a)
  have hrange : Set.range (algebraMap E' L) = Set.range (algebraMap E L) := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨eE a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨eE.symm a, by
        change algebraMap E L (eE (eE.symm a)) = algebraMap E L a
        rw [eE.apply_symm_apply]⟩
  have hgen' : Algebra.adjoin K (Set.range (algebraMap E' L)) = ⊤ := by
    rw [hrange]
    exact hgen
  have hdegree : Module.finrank k E' = Module.finrank k E := eE.toLinearEquiv.finrank_eq
  have hdeg' : Module.finrank K L = Module.finrank k E' := hdeg.trans hdegree.symm
  let Ω := AlgebraicClosure E'
  have tower : IsScalarTower k E' Ω := inferInstance
  have hAlg : Algebra.IsAlgebraic k Ω := Algebra.IsAlgebraic.trans k E' Ω
  obtain ⟨F, fieldF, algF, curveF, eftF, M, e, he⟩ :=
    SmoothProperCurve.exists_curveModel_iso_pullback_of_isAlgClosed k M₀.toBase Ω (specMap k Ω)
  simpa only [hdegree] using
    M₀.mem_picardNorm_range_iff_of_constantExtension M e he E' hgen' hdeg' x

/-- The norm quotient of an actual finite constant compositum is computed by degree. -/
def normQuotientEquivOfFiniteConstants
    (hC : ConstantsAreBase k K)
    (hgen : Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤)
    (hdeg : Module.finrank K L = Module.finrank k E) :
    (Pic k K ⧸ (norm (k := k) (K := K) (L := L)).range) ≃+ ZMod (Module.finrank k E) := by
  let d : Pic k K →+ ZMod (Module.finrank k E) :=
    (Int.castAddHom _).comp (H1Gm.degree k K)
  have hker : (norm (k := k) (K := K) (L := L)).range = d.ker := by
    ext x
    change x ∈ (norm (k := k) (K := K) (L := L)).range ↔
      (H1Gm.degree k K x : ZMod (Module.finrank k E)) = 0
    rw [mem_norm_range_iff_of_finite_constants hC hgen hdeg,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hs : Function.Surjective d := by
    obtain ⟨t, ht, hfin, -⟩ :=
      (isCurveOver_iff_exists_transcendental_finiteDimensional (K := k) (F := K)).mp
        (inferInstance : IsCurveOver k K)
    obtain ⟨D, hD⟩ := exists_divisor_degree_one_of_finite_constants ⟨t, ht, hfin⟩ hC
    have hd : d (H1Gm.mk D) = 1 := by
      change (Divisor.degree D : ZMod (Module.finrank k E)) = 1
      rw [hD, Int.cast_one]
    intro z
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective z
    refine ⟨a • H1Gm.mk D, ?_⟩
    rw [map_zsmul, hd, zsmul_eq_mul, mul_one]
    exact ha
  exact (QuotientAddGroup.quotientAddEquivOfEq hker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective d hs)

/-- The specified norm quotient sends each class to its actual degree modulo the
constant extension degree. -/
@[simp]
theorem normQuotientEquivOfFiniteConstants_mk
    (hC : ConstantsAreBase k K)
    (hgen : Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤)
    (hdeg : Module.finrank K L = Module.finrank k E) (x : Pic k K) :
    normQuotientEquivOfFiniteConstants hC hgen hdeg (QuotientAddGroup.mk x) =
      (H1Gm.degree k K x : ZMod (Module.finrank k E)) :=
  rfl

/-- The actual constant-compositum Picard norm index is its field degree. -/
theorem natCard_normQuotient_of_finite_constants
    (hC : ConstantsAreBase k K)
    (hgen : Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤)
    (hdeg : Module.finrank K L = Module.finrank k E) :
    Nat.card (Pic k K ⧸ (norm (k := k) (K := K) (L := L)).range) = Module.finrank K L := by
  have hn : NeZero (Module.finrank k E) := ⟨(Module.finrank_pos (R := k) (M := E)).ne'⟩
  rw [Nat.card_congr (normQuotientEquivOfFiniteConstants hC hgen hdeg).toEquiv,
    Nat.card_eq_fintype_card, ZMod.card, hdeg]

end AlgebraicCurve.Pic

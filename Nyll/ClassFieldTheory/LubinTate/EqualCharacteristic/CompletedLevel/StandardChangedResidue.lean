/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.StandardChangedUnramified
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedResidueFrobenius
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Actual residue maps for the completed standard/changed fields

The canonical spectral valuations on finite subfields agree with the restriction
of the ambient completed valuation. Their residue embeddings retain the actual
field inclusions. The changed fixed field has the original residue cardinality:
its embedded residues are fixed by cardinality-power Frobenius, and contain the
residue field of the Laurent base.
-/

@[expose] public section

noncomputable section

open scoped LaurentSeries PowerSeries ValuativeRel

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} [Field K]

noncomputable local instance standardChangedResidueBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  equalCharacteristicCompletedLevelBaseAlgebra F

noncomputable local instance standardChangedResidueLevelAlgebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra F.residueField⸨X⸩ (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelLaurentAlgebra F n

local instance standardChangedResidueScalarTower
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsScalarTower F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The chosen finite-subfield valuation is the restriction of the actual
ambient completed valuation, up to equivalence of value groups. -/
theorem equalCharacteristicCompletedFiniteSubfieldValuationIsEquiv
    (F : LocalField.{u, v} K) (n : ℕ)
    (T : IntermediateField F.residueField⸨X⸩ (equalCharacteristicCompletedLevelField F n))
    [FiniteDimensional F.residueField⸨X⸩ T] [Algebra.IsSeparable F.residueField⸨X⸩ T] :
    let : ValuativeRel F.residueField⸨X⸩ := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField F.residueField⸨X⸩ :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let : NontriviallyNormedField T := finiteExtensionSpectralNormedField F.residueField⸨X⸩ T
    let : ValuativeRel T := finiteExtensionSpectralValuativeRel F.residueField⸨X⸩ T
    let : IsNonarchimedeanLocalField T :=
      finiteExtensionSpectralIsNonarchimedeanLocalField F.residueField⸨X⸩ T
    (ValuativeRel.valuation T).IsEquiv
      ((equalCharacteristicCompletedLevelCompleteDVF F n).valuation.comap T.val.toRingHom) := by
  intro baseValuation baseLocalField targetNorm targetValuation targetLocalField
  let base := localCompleteDVF F.residueField⸨X⸩
  let coefficient := equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField
  let ambient := equalCharacteristicCompletedLevelCompleteDVF F n
  let : Valuation.HasExtension (ValuativeRel.valuation F.residueField⸨X⸩)
      (ValuativeRel.valuation T) :=
    finiteExtensionSpectralValuation_hasExtension F.residueField⸨X⸩ T
  let : base.valuation.HasExtension (localCompleteDVF T).valuation :=
    localCompleteDVFValuation_hasExtension F.residueField⸨X⸩ T
  let : base.valuation.HasExtension coefficient.valuation :=
    equalCharacteristicLaurentCompleteDVFValuation_hasExtension_completedBase F
  let : coefficient.valuation.HasExtension ambient.valuation :=
    equalCharacteristicCompletedLevelCompleteDVF_hasExtension F n
  let : base.valuation.HasExtension ambient.valuation :=
    ValuationTheory.DiscreteValuationField.Valuation.hasExtension_trans
      base.valuation coefficient.valuation ambient.valuation
  have inclusion_comp : T.val.toRingHom.comp (algebraMap F.residueField⸨X⸩ T) =
      algebraMap F.residueField⸨X⸩ (equalCharacteristicCompletedLevelField F n) := by
    ext x
    exact T.val.commutes x
  let : base.valuation.HasExtension (ambient.valuation.comap T.val.toRingHom) :=
    hasExtension_comap_of_algebraMap_compatible T.val.toRingHom inclusion_comp
  change (localCompleteDVF T).valuation.IsEquiv (ambient.valuation.comap T.val.toRingHom)
  exact valuation_isEquiv_of_finite_separable base (localCompleteDVF T)
    (ambient.valuation.comap T.val.toRingHom)

/-- Reduction of the actual finite-subfield inclusion into the completed level. -/
noncomputable def equalCharacteristicCompletedFiniteSubfieldResidueEmbedding
    (F : LocalField.{u, v} K) (n : ℕ)
    (T : IntermediateField F.residueField⸨X⸩ (equalCharacteristicCompletedLevelField F n))
    [FiniteDimensional F.residueField⸨X⸩ T] [Algebra.IsSeparable F.residueField⸨X⸩ T] :
    let : ValuativeRel F.residueField⸨X⸩ := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField F.residueField⸨X⸩ :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let : NontriviallyNormedField T := finiteExtensionSpectralNormedField F.residueField⸨X⸩ T
    let : ValuativeRel T := finiteExtensionSpectralValuativeRel F.residueField⸨X⸩ T
    let : IsNonarchimedeanLocalField T :=
      finiteExtensionSpectralIsNonarchimedeanLocalField F.residueField⸨X⸩ T
    𝓀[T] →+* (equalCharacteristicCompletedLevelCompleteDVF F n).residueField := by
  intro baseValuation baseLocalField targetNorm targetValuation targetLocalField
  exact residueFieldMapOfIsEquivComap (ValuativeRel.valuation T)
    (equalCharacteristicCompletedLevelCompleteDVF F n).valuation T.val.toRingHom
    (equalCharacteristicCompletedFiniteSubfieldValuationIsEquiv F n T)

/-- Residues of the genuine changed fixed field are fixed by the original
coefficient-cardinality Frobenius. -/
theorem equalCharacteristicCompletedFrobeniusFixedField_residue_pow_eq
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    let : ValuativeRel F.residueField⸨X⸩ := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField F.residueField⸨X⸩ :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let D := equalCharacteristicCompletedFrobeniusFixedField F a n
    let : NontriviallyNormedField D := finiteExtensionSpectralNormedField F.residueField⸨X⸩ D
    let : ValuativeRel D := finiteExtensionSpectralValuativeRel F.residueField⸨X⸩ D
    let : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField F.residueField⸨X⸩ D
    ∀ x : 𝓀[D], x ^ Nat.card F.residueField = x := by
  intro baseValuation baseLocalField D targetNorm targetValuation targetLocalField x
  let ambient := equalCharacteristicCompletedLevelCompleteDVF F n
  let hEquiv := equalCharacteristicCompletedFiniteSubfieldValuationIsEquiv F n D
  let embedding := equalCharacteristicCompletedFiniteSubfieldResidueEmbedding F n D
  let σ := equalCharacteristicCompletedFrobeniusIntegerEquiv F n a⁻¹
  have hcompat (b : (ValuativeRel.valuation D).valuationSubring) :
      valuationSubringMapOfIsEquivComap (ValuativeRel.valuation D) ambient.valuation
          D.val.toRingHom hEquiv ((RingEquiv.refl _) b) =
        σ (valuationSubringMapOfIsEquivComap (ValuativeRel.valuation D)
          ambient.valuation D.val.toRingHom hEquiv b) := by
    apply Subtype.ext
    change ((b : D) : equalCharacteristicCompletedLevelField F n) =
      equalCharacteristicCompletedFrobeniusLiftEquiv F n a⁻¹
        ((b : D) : equalCharacteristicCompletedLevelField F n)
    rw [← equalCharacteristicCompletedFrobeniusAlgEquiv_apply]
    exact (((IntermediateField.mem_fixedField_iff _ _).mp (b : D).property)
      (equalCharacteristicCompletedFrobeniusAlgEquiv F a n)
      (Subgroup.mem_zpowers (equalCharacteristicCompletedFrobeniusAlgEquiv F a n))).symm
  have hfixed := residueFieldMapOfIsEquivComap_mapEquiv
    (ValuativeRel.valuation D) ambient.valuation D.val.toRingHom hEquiv
    (RingEquiv.refl _) σ hcompat x
  change embedding (IsLocalRing.ResidueField.mapEquiv (RingEquiv.refl _) x) =
    IsLocalRing.ResidueField.mapEquiv σ (embedding x) at hfixed
  rw [IsLocalRing.ResidueField.mapEquiv_refl, RingEquiv.refl_apply] at hfixed
  apply embedding.injective
  rw [map_pow]
  exact (equalCharacteristicCompletedFrobeniusIntegerEquiv_residue_apply_eq_pow
    F n a⁻¹ (embedding x)).symm.trans hfixed.symm

/-- The ambient residue embedding intertwines the actual relative inverse
Frobenius with the inverse completed Frobenius on the actual integral closure. -/
theorem equalCharacteristicCompositumResidueEmbedding_inverseFrobenius
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    let : ValuativeRel F.residueField⸨X⸩ := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField F.residueField⸨X⸩ :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let D := equalCharacteristicCompletedFrobeniusFixedField F a n
    let : NontriviallyNormedField D := finiteExtensionSpectralNormedField F.residueField⸨X⸩ D
    let : ValuativeRel D := finiteExtensionSpectralValuativeRel F.residueField⸨X⸩ D
    let : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField F.residueField⸨X⸩ D
    let M := equalCharacteristicCompletedStandardChangedCompositum F a n
    let : NontriviallyNormedField M := finiteExtensionSpectralNormedField F.residueField⸨X⸩ M
    let : ValuativeRel M := finiteExtensionSpectralValuativeRel F.residueField⸨X⸩ M
    let : IsNonarchimedeanLocalField M :=
      finiteExtensionSpectralIsNonarchimedeanLocalField F.residueField⸨X⸩ M
    let : Valuation.HasExtension (ValuativeRel.valuation D) (ValuativeRel.valuation M) :=
      finiteExtensionSpectralValuation_hasExtension_of_tower F.residueField⸨X⸩ D M
    let : IsIntegralClosure 𝒪[M] 𝒪[D] M :=
      localCompleteDVF_integerRing_isIntegralClosure D M
    ∀ x : 𝓀[M],
      equalCharacteristicCompletedFiniteSubfieldResidueEmbedding F n M
          (galoisGroupResidueFieldEquivOfIsIntegralClosure D M
            (equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius F a n) x) =
        (IsLocalRing.ResidueField.mapEquiv
          (equalCharacteristicCompletedFrobeniusIntegerEquiv F n a⁻¹)).symm
            (equalCharacteristicCompletedFiniteSubfieldResidueEmbedding F n M x) := by
  intro baseValuation baseLocalField D changedNorm changedValuation changedLocalField
    M compositumNorm compositumValuation compositumLocalField extension integralClosure x
  let ambient := equalCharacteristicCompletedLevelCompleteDVF F n
  let hEquiv := equalCharacteristicCompletedFiniteSubfieldValuationIsEquiv F n M
  let τ := equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius F a n
  let σM := galoisGroupIntegerRingEquivOfIsIntegralClosure D M τ
  let σE := (equalCharacteristicCompletedFrobeniusIntegerEquiv F n a⁻¹).symm
  have hcompat (b : (ValuativeRel.valuation M).valuationSubring) :
      valuationSubringMapOfIsEquivComap (ValuativeRel.valuation M) ambient.valuation
          M.val.toRingHom hEquiv (σM b) =
        σE (valuationSubringMapOfIsEquivComap (ValuativeRel.valuation M)
          ambient.valuation M.val.toRingHom hEquiv b) := by
    apply Subtype.ext
    change ((τ (b : M)) : equalCharacteristicCompletedLevelField F n) =
      ((equalCharacteristicCompletedFrobeniusIntegerEquiv F n a⁻¹).symm
        (valuationSubringMapOfIsEquivComap (ValuativeRel.valuation M)
          ambient.valuation M.val.toRingHom hEquiv b) :
            equalCharacteristicCompletedLevelField F n)
    rw [equalCharacteristicCompletedFrobeniusIntegerEquiv_symm_coe]
    rw [show τ = equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius
        F a n by rfl,
      equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius_apply_coe]
    change (equalCharacteristicCompletedFrobeniusAlgEquiv F a n).symm
        ((b : M) : equalCharacteristicCompletedLevelField F n) =
      (equalCharacteristicCompletedFrobeniusLiftEquiv F n a⁻¹).symm
        ((b : M) : equalCharacteristicCompletedLevelField F n)
    apply (equalCharacteristicCompletedFrobeniusAlgEquiv F a n).injective
    rw [AlgEquiv.apply_symm_apply, equalCharacteristicCompletedFrobeniusAlgEquiv_apply,
      RingEquiv.apply_symm_apply]
  exact residueFieldMapOfIsEquivComap_mapEquiv
    (ValuativeRel.valuation M) ambient.valuation M.val.toRingHom hEquiv σM σE hcompat x

/-- The changed fixed field has exactly the original finite residue field
cardinality, using its actual embedding into the completed residue field. -/
theorem equalCharacteristicCompletedFrobeniusFixedField_residueField_card
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    let : ValuativeRel F.residueField⸨X⸩ := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField F.residueField⸨X⸩ :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let D := equalCharacteristicCompletedFrobeniusFixedField F a n
    let : NontriviallyNormedField D := finiteExtensionSpectralNormedField F.residueField⸨X⸩ D
    let : ValuativeRel D := finiteExtensionSpectralValuativeRel F.residueField⸨X⸩ D
    let : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField F.residueField⸨X⸩ D
    Nat.card 𝓀[D] = Nat.card F.residueField := by
  intro baseValuation baseLocalField D targetNorm targetValuation targetLocalField
  classical
  let : Fintype 𝓀[D] := Fintype.ofFinite 𝓀[D]
  have hq : 1 < Nat.card F.residueField := Finite.one_lt_card
  have hroots : (Finset.univ : Finset 𝓀[D]).val ⊆
      (Polynomial.X ^ Nat.card F.residueField - Polynomial.X : Polynomial 𝓀[D]).roots := by
    intro x _
    rw [Polynomial.mem_roots']
    refine ⟨FiniteField.X_pow_card_sub_X_ne_zero 𝓀[D] hq, ?_⟩
    change Polynomial.eval x
      (Polynomial.X ^ Nat.card F.residueField - Polynomial.X : Polynomial 𝓀[D]) = 0
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      equalCharacteristicCompletedFrobeniusFixedField_residue_pow_eq F a n x, sub_self]
  have hupper : Nat.card 𝓀[D] ≤ Nat.card F.residueField := by
    have h := Polynomial.card_le_degree_of_subset_roots hroots
    rw [Finset.card_univ, FiniteField.X_pow_card_sub_X_natDegree_eq 𝓀[D] hq] at h
    simpa only [Nat.card_eq_fintype_card] using h
  let : Valuation.HasExtension (ValuativeRel.valuation F.residueField⸨X⸩)
      (ValuativeRel.valuation D) :=
    finiteExtensionSpectralValuation_hasExtension F.residueField⸨X⸩ D
  let coefficientResidueEquiv : F.residueField ≃+* 𝓀[F.residueField⸨X⸩] :=
    (PowerSeries.residueFieldOfPowerSeries (k := F.residueField)).symm.trans
      (IsLocalRing.ResidueField.mapEquiv
        (powerSeriesEquivLaurentValuativeInteger F.residueField))
  let coefficientInclusion : F.residueField →+* 𝓀[D] :=
    (algebraMap 𝓀[F.residueField⸨X⸩] 𝓀[D]).comp coefficientResidueEquiv.toRingHom
  exact hupper.antisymm
    (Nat.card_le_card_of_injective coefficientInclusion coefficientInclusion.injective)

end EqualCharacteristic
end LubinTate

end

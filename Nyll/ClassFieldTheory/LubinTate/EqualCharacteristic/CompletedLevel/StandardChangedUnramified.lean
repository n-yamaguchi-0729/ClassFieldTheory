/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentLocalField
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormalizedIntegerValuation
public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationAddVal
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.StandardChangedGalois
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveUniformizer
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.AmbientUniformizer
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness

/-!
# The completed standard/changed compositum is unramified over the changed field

The genuine changed-uniformizer theta point is a uniformizer of the ambient
completed Lubin--Tate level.  Uniqueness of finite separable extensions of
the Laurent valuation transports this fact to both the changed fixed field and
the finite standard/changed compositum.  Since the same element is a
uniformizer on both sides, their relative ramification index is one.
-/



@[expose] public section

noncomputable section

open scoped LaurentSeries PowerSeries WithZero

universe u v

namespace LubinTate
namespace EqualCharacteristic

open scoped ValuativeRel

open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

noncomputable local instance standardChangedUnramifiedBaseAlgebra
    {K : Type u} [Field K] (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  equalCharacteristicCompletedLevelBaseAlgebra F

noncomputable local instance standardChangedUnramifiedLevelAlgebra
    {K : Type u} [Field K] (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra F.residueField⸨X⸩ (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelLaurentAlgebra F n

local instance standardChangedUnramifiedScalarTower
    {K : Type u} [Field K] (F : LocalField.{u, v} K) (n : ℕ) :
    IsScalarTower F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Coefficientwise Laurent extension preserves the actual valuation ring,
so its completed coefficient valuation extends the native local valuation. -/
theorem equalCharacteristicLaurentCompleteDVFValuation_hasExtension_completedBase
    {K : Type u} [Field K] (F : LocalField.{u, v} K) :
    let : ValuativeRel F.residueField⸨X⸩ := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField F.residueField⸨X⸩ :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    (localCompleteDVF F.residueField⸨X⸩).valuation.HasExtension
      (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).valuation := by
  intro baseValuativeRel baseLocalField
  let vB := (Valued.v : Valuation F.residueField⸨X⸩ ℤᵐ⁰)
  let : vB.Compatible := Valuation.Compatible.ofValuation vB
  let : vB.HasExtension
      (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).valuation := by
    apply Valuation.HasExtension.ofComapInteger
    ext x
    change (Valued.v : Valuation (AlgebraicClosure F.residueField)⸨X⸩ ℤᵐ⁰)
        (laurentSeriesCoefficientMap
          (algebraMap F.residueField (AlgebraicClosure F.residueField)) x) ≤ 1 ↔
      (Valued.v : Valuation F.residueField⸨X⸩ ℤᵐ⁰) x ≤ 1
    rw [LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero _ one_ne_zero,
      LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero _ one_ne_zero]
    simp only [laurentSeriesCoefficientMap_coeff, map_eq_zero]
  rw [localCompleteDVF_valuation_eq]
  exact hasExtension_of_isEquiv_base
    (ValuativeRel.isEquiv (ValuativeRel.valuation F.residueField⸨X⸩) vB)

/-- The changed prime element is a uniformizer both in the changed fixed
field and in the finite standard/changed compositum, when both finite fields
carry their canonical Laurent-base spectral valuations. -/
theorem
    equalCharacteristicCompletedFrobeniusPrimeElement_isUniformizer_in_changedField_and_compositum
    {K : Type u} [Field K] (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    let : ValuativeRel F.residueField⸨X⸩ := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField F.residueField⸨X⸩ :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let D := equalCharacteristicCompletedFrobeniusFixedField F a n
    let M := equalCharacteristicCompletedStandardChangedCompositum F a n
    let : NontriviallyNormedField D :=
      finiteExtensionSpectralNormedField F.residueField⸨X⸩ D
    let : ValuativeRel D :=
      finiteExtensionSpectralValuativeRel F.residueField⸨X⸩ D
    let : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField F.residueField⸨X⸩ D
    let : NontriviallyNormedField M :=
      finiteExtensionSpectralNormedField F.residueField⸨X⸩ M
    let : ValuativeRel M :=
      finiteExtensionSpectralValuativeRel F.residueField⸨X⸩ M
    let : IsNonarchimedeanLocalField M :=
      finiteExtensionSpectralIsNonarchimedeanLocalField F.residueField⸨X⸩ M
    (localCompleteDVF D).valuation.IsUniformizer
        (equalCharacteristicCompletedFrobeniusPrimeElement F a n : D) ∧
      (localCompleteDVF M).valuation.IsUniformizer
        (algebraMap D M
          (equalCharacteristicCompletedFrobeniusPrimeElement F a n)) := by
  intro baseValuativeRel baseLocalField D M
    changedNorm changedValuation changedLocalField compositumNorm compositumValuation
    compositumLocalField
  let E := equalCharacteristicCompletedLevelField F n
  let canonicalBase := localCompleteDVF F.residueField⸨X⸩
  let coefficient := equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField
  let ambient := equalCharacteristicCompletedLevelCompleteDVF F n
  let :
      Valuation.HasExtension (ValuativeRel.valuation F.residueField⸨X⸩)
        (ValuativeRel.valuation D) :=
    finiteExtensionSpectralValuation_hasExtension F.residueField⸨X⸩ D
  let :
      Valuation.HasExtension (ValuativeRel.valuation F.residueField⸨X⸩)
        (ValuativeRel.valuation M) :=
    finiteExtensionSpectralValuation_hasExtension F.residueField⸨X⸩ M
  let :
      canonicalBase.valuation.HasExtension
        (localCompleteDVF D).valuation :=
    localCompleteDVFValuation_hasExtension F.residueField⸨X⸩ D
  let :
      canonicalBase.valuation.HasExtension
        (localCompleteDVF M).valuation :=
    localCompleteDVFValuation_hasExtension F.residueField⸨X⸩ M
  let : canonicalBase.valuation.HasExtension coefficient.valuation :=
    equalCharacteristicLaurentCompleteDVFValuation_hasExtension_completedBase F
  let : coefficient.valuation.HasExtension ambient.valuation :=
    equalCharacteristicCompletedLevelCompleteDVF_hasExtension F n
  let : canonicalBase.valuation.HasExtension ambient.valuation :=
    ValuationTheory.DiscreteValuationField.Valuation.hasExtension_trans
      canonicalBase.valuation coefficient.valuation ambient.valuation
  let inclusionD : D →+* E := D.val.toRingHom
  have inclusionD_comp :
      inclusionD.comp (algebraMap F.residueField⸨X⸩ D) =
        algebraMap F.residueField⸨X⸩ E := by
    ext x
    exact D.val.commutes x
  let :
      canonicalBase.valuation.HasExtension
        (ambient.valuation.comap inclusionD) :=
    hasExtension_comap_of_algebraMap_compatible
      inclusionD inclusionD_comp
  let inclusionM : M →+* E := M.val.toRingHom
  have inclusionM_comp :
      inclusionM.comp (algebraMap F.residueField⸨X⸩ M) =
        algebraMap F.residueField⸨X⸩ E := by
    ext x
    exact M.val.commutes x
  let :
      canonicalBase.valuation.HasExtension
        (ambient.valuation.comap inclusionM) :=
    hasExtension_comap_of_algebraMap_compatible
      inclusionM inclusionM_comp
  have hthetaAmbient :
      ambient.valuation.IsUniformizer
        (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n : E) :=
    equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_isUniformizer F a n
  have hthetaD :
      (localCompleteDVF D).valuation.IsUniformizer
        (equalCharacteristicCompletedFrobeniusPrimeElement F a n : D) := by
    apply
      isUniformizer_of_ambient_image_isUniformizer
        canonicalBase (localCompleteDVF D) ambient inclusionD
    change
      ambient.valuation.IsUniformizer
        (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n : E)
    exact hthetaAmbient
  have hthetaM :
      (localCompleteDVF M).valuation.IsUniformizer
        (algebraMap D M
          (equalCharacteristicCompletedFrobeniusPrimeElement F a n)) := by
    apply
      isUniformizer_of_ambient_image_isUniformizer
        canonicalBase (localCompleteDVF M) ambient inclusionM
    change
      ambient.valuation.IsUniformizer
        (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n : E)
    exact hthetaAmbient
  exact ⟨hthetaD, hthetaM⟩

/-- The finite standard/changed compositum has relative ramification index
one over the changed fixed field. -/
theorem
    equalCharacteristicCompletedStandardChangedCompositum_ramificationIndex_eq_one
    {K : Type u} [Field K] (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    let : ValuativeRel F.residueField⸨X⸩ := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField F.residueField⸨X⸩ :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let D := equalCharacteristicCompletedFrobeniusFixedField F a n
    let M := equalCharacteristicCompletedStandardChangedCompositum F a n
    let : NontriviallyNormedField D :=
      finiteExtensionSpectralNormedField F.residueField⸨X⸩ D
    let : ValuativeRel D :=
      finiteExtensionSpectralValuativeRel F.residueField⸨X⸩ D
    let : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField F.residueField⸨X⸩ D
    let : NontriviallyNormedField M :=
      finiteExtensionSpectralNormedField F.residueField⸨X⸩ M
    let : ValuativeRel M :=
      finiteExtensionSpectralValuativeRel F.residueField⸨X⸩ M
    let : IsNonarchimedeanLocalField M :=
      finiteExtensionSpectralIsNonarchimedeanLocalField F.residueField⸨X⸩ M
    let :
        Valuation.HasExtension (ValuativeRel.valuation D)
          (ValuativeRel.valuation M) :=
      finiteExtensionSpectralValuation_hasExtension_of_tower F.residueField⸨X⸩ D M
    let :
        (localCompleteDVF D).valuation.HasExtension
          (localCompleteDVF M).valuation :=
      localCompleteDVFValuation_hasExtension D M
    ramificationIndex (localCompleteDVF D).toDVF
      (localCompleteDVF M).toDVF = 1 := by
  intro baseValuativeRel baseLocalField D M changedNorm changedValuation changedLocalField
    compositumNorm compositumValuation compositumLocalField valuationExtension completeExtension
  let base := localCompleteDVF D
  let target := localCompleteDVF M
  obtain ⟨hthetaD, hthetaM⟩ :=
    equalCharacteristicCompletedFrobeniusPrimeElement_isUniformizer_in_changedField_and_compositum
      F a n
  let thetaInteger : base.valuationSubring :=
    ⟨equalCharacteristicCompletedFrobeniusPrimeElement F a n,
      hthetaD.val_lt_one.le⟩
  have hthetaMap :
      target.valuation.IsUniformizer
        (((integerMap base.toDVF target.toDVF thetaInteger :
          target.valuationSubring) : M)) := by
    rw [integerMap_apply]
    exact hthetaM
  exact
    ValuedExtension.ramificationIndex_eq_one_of_integerMap_uniformizer
      base target thetaInteger
      (by simpa only [thetaInteger] using hthetaD)
      hthetaMap

/-- With the canonical Laurent-base spectral valuations, the finite
standard/changed compositum is an unramified valued extension of the changed
fixed field. -/
theorem
    equalCharacteristicCompletedStandardChangedCompositum_isUnramifiedValuedExtension
    {K : Type u} [Field K] (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    let : ValuativeRel F.residueField⸨X⸩ := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField F.residueField⸨X⸩ :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let D := equalCharacteristicCompletedFrobeniusFixedField F a n
    let M := equalCharacteristicCompletedStandardChangedCompositum F a n
    let : FiniteDimensional D M :=
      FiniteDimensional.right F.residueField⸨X⸩ D M
    let : Algebra.IsSeparable D M :=
      Algebra.isSeparable_tower_top_of_isSeparable
        (F := F.residueField⸨X⸩) (L := D) (E := M)
    let : NontriviallyNormedField D :=
      finiteExtensionSpectralNormedField F.residueField⸨X⸩ D
    let : ValuativeRel D :=
      finiteExtensionSpectralValuativeRel F.residueField⸨X⸩ D
    let : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField F.residueField⸨X⸩ D
    let : NontriviallyNormedField M :=
      finiteExtensionSpectralNormedField F.residueField⸨X⸩ M
    let : ValuativeRel M :=
      finiteExtensionSpectralValuativeRel F.residueField⸨X⸩ M
    let : IsNonarchimedeanLocalField M :=
      finiteExtensionSpectralIsNonarchimedeanLocalField F.residueField⸨X⸩ M
    let :
        Valuation.HasExtension (ValuativeRel.valuation D)
          (ValuativeRel.valuation M) :=
      finiteExtensionSpectralValuation_hasExtension_of_tower F.residueField⸨X⸩ D M
    let :
        (localCompleteDVF D).valuation.HasExtension
          (localCompleteDVF M).valuation :=
      localCompleteDVFValuation_hasExtension D M
    let :
        IsScalarTower (localCompleteDVF D).valuationSubring
          (localCompleteDVF M).valuationSubring M :=
      IsScalarTower.of_algebraMap_eq' rfl
    let :
        Module.Finite (ValuativeRel.valuation D).integer
          (ValuativeRel.valuation M).integer := by
      change
        Module.Finite (localCompleteDVF D).valuationSubring
          (localCompleteDVF M).valuationSubring
      exact
        moduleFinite_target_valuationSubring_of_finite_separable
          (localCompleteDVF D) (localCompleteDVF M)
    LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      D M := by
  intro baseValuativeRel baseLocalField D M relativeFinite relativeSeparable
    changedNorm changedValuation changedLocalField compositumNorm compositumValuation
    compositumLocalField valuationExtension completeExtension integerTower integerFinite
  let base := localCompleteDVF D
  let target := localCompleteDVF M
  let :
      Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable
      base target
  have hramification :
      ramificationIndex base.toDVF target.toDVF = 1 :=
    equalCharacteristicCompletedStandardChangedCompositum_ramificationIndex_eq_one
      F a n
  exact {
    maximalIdeal_ramificationIdx_eq_one := by
      change target.maximalIdeal.ramificationIdx base.valuationSubring = 1
      have hbaseMaximal_ne :
          (base.maximalIdeal : Ideal base.valuationSubring) ≠ ⊥ :=
        Ring.ne_bot_of_isMaximal_of_not_isField
          (IsLocalRing.maximalIdeal.isMaximal base.valuationSubring)
          (IsDiscreteValuationRing.not_isField base.valuationSubring)
      rw [← Ideal.ramificationIdx'_eq_ramificationIdx
        base.maximalIdeal target.maximalIdeal hbaseMaximal_ne]
      exact hramification
  }

end EqualCharacteristic
end LubinTate

end

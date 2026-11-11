/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseNaturality
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseFrobenius
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseSemilinearNaturality
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.EqualCharacteristicArtinNormalization
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.StandardChangedFrobenius
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.UnitActionRestriction

/-!
# Native local Artin values on equal-characteristic Lubin--Tate levels

The changed-prime norm is `aT`. The relative extension is actually unramified,
with inverse completed Frobenius as geometric Frobenius. Native Artin sends
the negative changed prime to that inverse Frobenius, and norm--restriction
therefore gives the direct `[a]` action on the original chosen primitive point.

The existing explicit homomorphism acts by `[a⁻¹]`; the comparison below
retains that definition and evaluates it at the inverse input unit.
For an arbitrary nonzero Laurent series, the actual unit-factor extraction
extends the comparison to the full field unit group, compatibly with finite
restriction and specified semilinear equivalences.
-/

@[expose] public section

noncomputable section

open scoped ValuativeRel LaurentSeries PowerSeries

universe u v w z

namespace LocalClassFieldTheory

open LubinTate LubinTate.EqualCharacteristic
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.ValuedExtension
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} [Field K]

noncomputable local instance equalCharacteristicArtinComparisonBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  equalCharacteristicCompletedLevelBaseAlgebra F

noncomputable local instance equalCharacteristicArtinComparisonLevelAlgebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra F.residueField⸨X⸩ (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelLaurentAlgebra F n

/-- The negative changed-uniformizer prime element as an actual unit of its
completed fixed field. Its norm is the changed base uniformizer `aT`. -/
noncomputable def equalCharacteristicCompletedFrobeniusNegativePrimeUnit
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    (equalCharacteristicCompletedFrobeniusFixedField F a n)ˣ :=
  Units.mk0 (-equalCharacteristicCompletedFrobeniusPrimeElement F a n) (by
    have hnorm : Algebra.norm F.residueField⸨X⸩
        (-equalCharacteristicCompletedFrobeniusPrimeElement F a n) ≠ 0 := by
      rw [equalCharacteristicCompletedFrobenius_norm_neg_primeElement]
      exact equalCharacteristicChangedLaurentUniformizer_ne_zero F a
    intro hz
    apply hnorm
    rw [hz, Algebra.norm_zero])

/-- The underlying field element of the negative changed prime unit is
`-theta`. -/
@[simp]
theorem equalCharacteristicCompletedFrobeniusNegativePrimeUnit_coe
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    (equalCharacteristicCompletedFrobeniusNegativePrimeUnit F n a :
      equalCharacteristicCompletedFrobeniusFixedField F a n) =
      -equalCharacteristicCompletedFrobeniusPrimeElement F a n :=
  rfl

/-- The field-unit norm of the negative changed prime is the actual
changed base uniformizer. -/
theorem equalCharacteristicCompletedFrobeniusNegativePrimeUnit_norm
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    normUnits F.residueField⸨X⸩
        (equalCharacteristicCompletedFrobeniusFixedField F a n)
        (equalCharacteristicCompletedFrobeniusNegativePrimeUnit F n a) =
      equalCharacteristicChangedLaurentUniformizerUnit F a := by
  apply Units.ext
  simpa only [normUnits_apply_coe,
    equalCharacteristicCompletedFrobeniusNegativePrimeUnit_coe] using
    (equalCharacteristicCompletedFrobenius_norm_neg_primeElement F a n).trans
      (equalCharacteristicChangedLaurentUniformizerUnit_coe F a).symm

/-- The negative changed prime has normalized additive value `-1` in its
completed fixed field. -/
theorem equalCharacteristicCompletedFrobeniusNegativePrimeUnit_valuationMap
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    let : ValuativeRel F.residueField⸨X⸩ := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField F.residueField⸨X⸩ :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let D := equalCharacteristicCompletedFrobeniusFixedField F a n
    let : NontriviallyNormedField D :=
      finiteExtensionSpectralNormedField F.residueField⸨X⸩ D
    let : ValuativeRel D :=
      finiteExtensionSpectralValuativeRel F.residueField⸨X⸩ D
    let : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField F.residueField⸨X⸩ D
    IsNonarchimedeanLocalField.valuationMap D
        (Additive.ofMul
          (equalCharacteristicCompletedFrobeniusNegativePrimeUnit F n a)) =
      -1 := by
  intro baseValuativeRel baseLocalField D changedNorm changedValuation changedLocalField
  let M := equalCharacteristicCompletedStandardChangedCompositum F a n
  let : NontriviallyNormedField M :=
    finiteExtensionSpectralNormedField F.residueField⸨X⸩ M
  let : ValuativeRel M :=
    finiteExtensionSpectralValuativeRel F.residueField⸨X⸩ M
  let : IsNonarchimedeanLocalField M :=
    finiteExtensionSpectralIsNonarchimedeanLocalField F.residueField⸨X⸩ M
  obtain ⟨htheta, _⟩ :=
    equalCharacteristicCompletedFrobeniusPrimeElement_isUniformizer_in_changedField_and_compositum
      F a n
  have hnegative :
      (localCompleteDVF D).valuation.IsUniformizer
        (-equalCharacteristicCompletedFrobeniusPrimeElement F a n : D) := by
    simpa only [Valuation.IsUniformizer.iff,
      (localCompleteDVF D).valuation.map_neg] using htheta
  let negativeInteger : (localCompleteDVF D).valuationSubring :=
    ⟨-equalCharacteristicCompletedFrobeniusPrimeElement F a n,
      hnegative.val_lt_one.le⟩
  have hunit :
      equalCharacteristicCompletedFrobeniusNegativePrimeUnit F n a =
        IsNonarchimedeanLocalField.uniformizerFieldUnit
          D negativeInteger hnegative := by
    apply Units.ext
    rfl
  rw [hunit]
  exact
    IsNonarchimedeanLocalField.valuationMap_uniformizerFieldUnit
      D negativeInteger hnegative

/-- The actual relative local Artin image of the negative changed prime is
the actual relative inverse completed Frobenius. -/
theorem
    equalCharacteristicCompletedFrobeniusRelativeArtin_negativePrime
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
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
    let : Module.Finite 𝒪[D] 𝒪[M] := localCompleteDVF_integerRing_moduleFinite D M
    let :
        IsNonarchimedeanLocalField.IsUnramifiedValuedExtension D M :=
      equalCharacteristicCompletedStandardChangedCompositum_isUnramifiedValuedExtension
        F a n
    Universe.abelianLocalArtinMonoidHom D M
        (equalCharacteristicCompletedFrobeniusNegativePrimeUnit F n a) =
      equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius F a n := by
  intro baseValuativeRel baseLocalField D M changedNorm changedValuation changedLocalField
    compositumNorm compositumValuation compositumLocalField valuationExtension
    integerFinite unramifiedExtension
  let : IsIntegralClosure 𝒪[M] 𝒪[D] M :=
    localCompleteDVF_integerRing_isIntegralClosure D M
  calc
    Universe.abelianLocalArtinMonoidHom D M
        (equalCharacteristicCompletedFrobeniusNegativePrimeUnit F n a) =
        (arithmeticFrobeniusOfUnramifiedValuation D M) ^
          IsNonarchimedeanLocalField.valuationMap D
            (Additive.ofMul
              (equalCharacteristicCompletedFrobeniusNegativePrimeUnit F n a)) :=
      Universe.abelianLocalArtinMonoidHom_eq_frobenius_zpow D M _
    _ = (arithmeticFrobeniusOfUnramifiedValuation D M) ^ (-1 : ℤ) := by
      rw [equalCharacteristicCompletedFrobeniusNegativePrimeUnit_valuationMap]
    _ = (arithmeticFrobeniusOfUnramifiedValuation D M)⁻¹ := by
      rw [zpow_neg_one]
    _ = equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius F a n :=
      (equalCharacteristicRelativeInverseFrobenius_eq_inverseArithmeticFrobenius
        F a n).symm

/-- Restriction of the actual relative inverse Frobenius to the original
level is the direct unit action, with the specified embedding. -/
theorem equalCharacteristicCompletedRelativeInverseFrobenius_restrict_standardLevel
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    let B := F.residueField⸨X⸩
    let T := equalCharacteristicLubinTateLevelField F n
    let M := equalCharacteristicCompletedStandardChangedCompositum F a n
    let : Algebra T M :=
      (equalCharacteristicStandardLevelToCompletedChangedCompositum F a n).toRingHom.toAlgebra
    let : IsScalarTower B T M :=
      IsScalarTower.of_algebraMap_eq'
        (equalCharacteristicStandardLevelToCompletedChangedCompositum F a n).comp_algebraMap.symm
    ((AlgEquiv.restrictNormalHom T).comp (AlgEquiv.restrictScalarsHom B))
        (equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius F a n) =
      equalCharacteristicLubinTateArtinUnitToGal F n a⁻¹ := by
  intro B T M standardAlgebra standardTower
  apply AlgEquiv.ext
  intro x
  apply (algebraMap T M).injective
  rw [MonoidHom.comp_apply, AlgEquiv.restrictScalarsHom_apply]
  change algebraMap T M
      (AlgEquiv.restrictNormal
        ((AlgEquiv.restrictScalarsHom B)
          (equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius F a n)) T x) = _
  rw [AlgEquiv.restrictNormal_commutes]
  change equalCharacteristicCompletedStandardChangedInverseFrobenius F a n
      (equalCharacteristicStandardLevelToCompletedChangedCompositum F a n x) =
    equalCharacteristicStandardLevelToCompletedChangedCompositum F a n
      (equalCharacteristicLubinTateArtinUnitToGal F n a⁻¹ x)
  exact equalCharacteristicCompletedStandardChangedInverseFrobenius_standardLevel F a n x

/-- Native geometric Artin on a power-series unit is the direct unit bracket.
The existing explicit inverse-bracket homomorphism is evaluated at `a⁻¹`.
This is the pointwise norm--restriction comparison, not a kernel comparison. -/
theorem equalCharacteristicAbelianLocalArtin_eq_explicitUnitAction
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    let B := F.residueField⸨X⸩
    let T := equalCharacteristicLubinTateLevelField F n
    let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let : FiniteDimensional B T := equalCharacteristicLubinTateLevelField_finiteDimensional F n
    Universe.abelianLocalArtinMonoidHom B T
        (equalCharacteristicPowerSeriesUnitToLaurentFieldUnit F a) =
      equalCharacteristicLubinTateArtinUnitToGal F n a⁻¹ := by
  intro B T baseValuativeRel baseLocalField standardFinite
  let D := equalCharacteristicCompletedFrobeniusFixedField F a n
  let M := equalCharacteristicCompletedStandardChangedCompositum F a n
  let : Algebra T M :=
    (equalCharacteristicStandardLevelToCompletedChangedCompositum F a n).toRingHom.toAlgebra
  let : IsScalarTower B T M :=
    IsScalarTower.of_algebraMap_eq'
      (equalCharacteristicStandardLevelToCompletedChangedCompositum F a n).comp_algebraMap.symm
  let : NontriviallyNormedField D := finiteExtensionSpectralNormedField B D
  let : ValuativeRel D := finiteExtensionSpectralValuativeRel B D
  let : IsNonarchimedeanLocalField D := finiteExtensionSpectralIsNonarchimedeanLocalField B D
  let : NontriviallyNormedField M := finiteExtensionSpectralNormedField B M
  let : ValuativeRel M := finiteExtensionSpectralValuativeRel B M
  let : IsNonarchimedeanLocalField M := finiteExtensionSpectralIsNonarchimedeanLocalField B M
  let : Valuation.HasExtension (ValuativeRel.valuation B) (ValuativeRel.valuation D) :=
    finiteExtensionSpectralValuation_hasExtension B D
  let : Valuation.HasExtension (ValuativeRel.valuation D) (ValuativeRel.valuation M) :=
    finiteExtensionSpectralValuation_hasExtension_of_tower B D M
  let : Module.Finite 𝒪[D] 𝒪[M] := localCompleteDVF_integerRing_moduleFinite D M
  let : IsNonarchimedeanLocalField.IsUnramifiedValuedExtension D M :=
    equalCharacteristicCompletedStandardChangedCompositum_isUnramifiedValuedExtension F a n
  have hnormRestriction := DFunLike.congr_fun
    (Universe.abelianLocalArtinMonoidHom_norm_restriction B D T M)
    (equalCharacteristicCompletedFrobeniusNegativePrimeUnit F n a)
  have hrelative : Universe.abelianLocalArtinMonoidHom D M
      (equalCharacteristicCompletedFrobeniusNegativePrimeUnit F n a) =
        equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius F a n :=
    equalCharacteristicCompletedFrobeniusRelativeArtin_negativePrime F n a
  have hrestrict :
      ((AlgEquiv.restrictNormalHom T).comp (AlgEquiv.restrictScalarsHom B))
          (equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius F a n) =
        equalCharacteristicLubinTateArtinUnitToGal F n a⁻¹ :=
    equalCharacteristicCompletedRelativeInverseFrobenius_restrict_standardLevel F n a
  have hnorm : normUnits B D
      (equalCharacteristicCompletedFrobeniusNegativePrimeUnit F n a) =
        equalCharacteristicChangedLaurentUniformizerUnit F a :=
    equalCharacteristicCompletedFrobeniusNegativePrimeUnit_norm F n a
  have hchanged : Universe.abelianLocalArtinMonoidHom B T
      (equalCharacteristicChangedLaurentUniformizerUnit F a) =
        Universe.abelianLocalArtinMonoidHom B T
          (equalCharacteristicPowerSeriesUnitToLaurentFieldUnit F a) :=
    equalCharacteristicAbelianLocalArtin_changedUniformizer F n a
  exact (show equalCharacteristicLubinTateArtinUnitToGal F n a⁻¹ =
      Universe.abelianLocalArtinMonoidHom B T
        (equalCharacteristicPowerSeriesUnitToLaurentFieldUnit F a) by
    simpa only [MonoidHom.comp_apply, hrelative, hrestrict, hnorm, hchanged]
      using hnormRestriction).symm

/-- The native Artin action on the actual chosen primitive point is `[a]`. -/
theorem equalCharacteristicAbelianLocalArtin_apply_primitiveRoot
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    let B := F.residueField⸨X⸩
    let T := equalCharacteristicLubinTateLevelField F n
    let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField B := equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let : FiniteDimensional B T := equalCharacteristicLubinTateLevelField_finiteDimensional F n
    ((Universe.abelianLocalArtinMonoidHom B T
          (equalCharacteristicPowerSeriesUnitToLaurentFieldUnit F a))
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen : SeparableClosure B) =
      equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        (a : F.residueField⟦X⟧) (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) := by
  intro B T baseValuativeRel baseLocalField standardFinite
  rw [equalCharacteristicAbelianLocalArtin_eq_explicitUnitAction F n a]
  exact equalCharacteristicLubinTateArtinUnitToGal_inv_apply_gen_coe F n a

/-- The pointwise comparison is compatible with restriction to every lower
actual finite level, without any compatibility assumption on chosen roots. -/
theorem equalCharacteristicAbelianLocalArtin_explicitUnitAction_restrict
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    {m n : ℕ} (hmn : m ≤ n) (a : F.residueField⟦X⟧ˣ) :
    let B := F.residueField⸨X⸩
    let T := equalCharacteristicLubinTateLevelField F n
    let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField B := equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let : FiniteDimensional B T := equalCharacteristicLubinTateLevelField_finiteDimensional F n
    RamificationTheory.intermediateFieldRestrictNormalHom
        (equalCharacteristicLubinTateLevelField F m) T
        (equalCharacteristicLubinTateLevelField_mono F hmn)
        (Universe.abelianLocalArtinMonoidHom B T
          (equalCharacteristicPowerSeriesUnitToLaurentFieldUnit F a)) =
      equalCharacteristicLubinTateArtinUnitToGal F m a⁻¹ := by
  intro B T baseValuativeRel baseLocalField standardFinite
  rw [equalCharacteristicAbelianLocalArtin_eq_explicitUnitAction F n a]
  exact equalCharacteristicLubinTateArtinUnitToGal_restrict F hmn a⁻¹

/-- The explicit pointwise action commutes with the specified semilinear
equivalences of the actual base and extension fields. The target fields have
independent universes, and the original equivalences remain in the formula. -/
theorem equalCharacteristicAbelianLocalArtin_explicitUnitAction_semilinear
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic] (n : ℕ)
    (B' : Type w) (T' : Type z)
    [Field B'] [ValuativeRel B'] [TopologicalSpace B'] [IsNonarchimedeanLocalField B']
    [Field T'] [Algebra B' T'] [FiniteDimensional B' T'] [IsAbelianGalois B' T']
    (eB : F.residueField⸨X⸩ ≃+* B')
    (eT : equalCharacteristicLubinTateLevelField F n ≃+* T')
    (hcomm : ∀ b : F.residueField⸨X⸩,
      eT (algebraMap F.residueField⸨X⸩ (equalCharacteristicLubinTateLevelField F n) b) =
        algebraMap B' T' (eB b))
    (a : F.residueField⟦X⟧ˣ) (x : equalCharacteristicLubinTateLevelField F n) :
    let B := F.residueField⸨X⸩
    let T := equalCharacteristicLubinTateLevelField F n
    let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField B := equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let : FiniteDimensional B T := equalCharacteristicLubinTateLevelField_finiteDimensional F n
    SemilinearValuationCompatible B B' eB →
      eT (equalCharacteristicLubinTateArtinUnitToGal F n a⁻¹ x) =
        Universe.abelianLocalArtinMonoidHom B' T'
          (Units.map eB.toMonoidHom (equalCharacteristicPowerSeriesUnitToLaurentFieldUnit F a))
          (eT x) := by
  intro B T baseValuativeRel baseLocalField standardFinite hExt
  have h := Universe.abelianLocalArtinMonoidHom_semilinear_action
    B B' T T' eB eT hcomm hExt
    (equalCharacteristicPowerSeriesUnitToLaurentFieldUnit F a) x
  rw [equalCharacteristicAbelianLocalArtin_eq_explicitUnitAction F n a] at h
  exact h

/-- The full native Artin map on every nonzero Laurent series is the
explicit action of its actual power-series unit factor. Both signs use the
same normalized parameter `T⁻¹` as the native valuation map. -/
theorem equalCharacteristicAbelianLocalArtin_eq_explicitLaurentAction
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (n : ℕ) (x : F.residueField⸨X⸩ˣ) :
    let B := F.residueField⸨X⸩
    let T := equalCharacteristicLubinTateLevelField F n
    let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField B := equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let : FiniteDimensional B T := equalCharacteristicLubinTateLevelField_finiteDimensional F n
    Universe.abelianLocalArtinMonoidHom B T x =
      equalCharacteristicLubinTateArtinUnitToGal F n
        (equalCharacteristicLaurentPowerSeriesUnitPart F x)⁻¹ := by
  intro B T valuationOwner localFieldOwner finiteOwner
  let artin : Bˣ →* Gal(T/B) := Universe.abelianLocalArtinMonoidHom B T
  let a := equalCharacteristicLaurentPowerSeriesUnitPart F x
  let t : Bˣ := (equalCharacteristicLaurentUniformizerUnit F)⁻¹
  let z := IsNonarchimedeanLocalField.valuationMap B (Additive.ofMul x)
  have ht : artin t = 1 := equalCharacteristicAbelianLocalArtin_normalizedUniformizer F n
  have hpow : artin (t ^ z) = 1 :=
    (artin.map_zpow t z).trans
      ((congrArg (fun g : Gal(T/B) => g ^ z) ht).trans (one_zpow z))
  have hdiv : artin (x / t ^ z) = artin x :=
    (artin.map_div x (t ^ z)).trans
      ((congrArg (fun g : Gal(T/B) => artin x / g) hpow).trans (div_one (artin x)))
  change artin x = equalCharacteristicLubinTateArtinUnitToGal F n a⁻¹
  calc
    artin x = artin (x / t ^ z) := hdiv.symm
    _ = artin (equalCharacteristicPowerSeriesUnitToLaurentFieldUnit F a) :=
      congrArg artin (equalCharacteristicLaurentPowerSeriesUnitPart_include F x).symm
    _ = _ := equalCharacteristicAbelianLocalArtin_eq_explicitUnitAction F n a

/-- Every Laurent field unit acts on the actual chosen primitive point by
the direct bracket of its extracted power-series factor. -/
theorem equalCharacteristicAbelianLocalArtin_laurentUnit_apply_primitiveRoot
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (n : ℕ) (x : F.residueField⸨X⸩ˣ) :
    let B := F.residueField⸨X⸩
    let T := equalCharacteristicLubinTateLevelField F n
    let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField B := equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let : FiniteDimensional B T := equalCharacteristicLubinTateLevelField_finiteDimensional F n
    ((Universe.abelianLocalArtinMonoidHom B T x)
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen : SeparableClosure B) =
      equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        (equalCharacteristicLaurentPowerSeriesUnitPart F x : F.residueField⟦X⟧)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) := by
  intro B T valuationOwner localFieldOwner finiteOwner
  rw [equalCharacteristicAbelianLocalArtin_eq_explicitLaurentAction F n x]
  exact equalCharacteristicLubinTateArtinUnitToGal_inv_apply_gen_coe
    F n (equalCharacteristicLaurentPowerSeriesUnitPart F x)

/-- The full Laurent-unit formula restricts to each lower actual level
using the same unit factor, which is independent of the level. -/
theorem equalCharacteristicAbelianLocalArtin_laurentUnit_restrict
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    {m n : ℕ} (hmn : m ≤ n) (x : F.residueField⸨X⸩ˣ) :
    let B := F.residueField⸨X⸩
    let T := equalCharacteristicLubinTateLevelField F n
    let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField B := equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let : FiniteDimensional B T := equalCharacteristicLubinTateLevelField_finiteDimensional F n
    RamificationTheory.intermediateFieldRestrictNormalHom
        (equalCharacteristicLubinTateLevelField F m) T
        (equalCharacteristicLubinTateLevelField_mono F hmn)
        (Universe.abelianLocalArtinMonoidHom B T x) =
      equalCharacteristicLubinTateArtinUnitToGal F m
        (equalCharacteristicLaurentPowerSeriesUnitPart F x)⁻¹ := by
  intro B T valuationOwner localFieldOwner finiteOwner
  rw [equalCharacteristicAbelianLocalArtin_eq_explicitLaurentAction F n x]
  exact equalCharacteristicLubinTateArtinUnitToGal_restrict
    F hmn (equalCharacteristicLaurentPowerSeriesUnitPart F x)⁻¹

/-- The full Laurent-unit action commutes with the specified semilinear
equivalences, retaining the actual field unit and both original maps. -/
theorem equalCharacteristicAbelianLocalArtin_explicitLaurentAction_semilinear
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic] (n : ℕ)
    (B' : Type w) (T' : Type z)
    [Field B'] [ValuativeRel B'] [TopologicalSpace B'] [IsNonarchimedeanLocalField B']
    [Field T'] [Algebra B' T'] [FiniteDimensional B' T'] [IsAbelianGalois B' T']
    (eB : F.residueField⸨X⸩ ≃+* B')
    (eT : equalCharacteristicLubinTateLevelField F n ≃+* T')
    (hcomm : ∀ b : F.residueField⸨X⸩,
      eT (algebraMap F.residueField⸨X⸩ (equalCharacteristicLubinTateLevelField F n) b) =
        algebraMap B' T' (eB b))
    (x : F.residueField⸨X⸩ˣ) (y : equalCharacteristicLubinTateLevelField F n) :
    let B := F.residueField⸨X⸩
    let T := equalCharacteristicLubinTateLevelField F n
    let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField B := equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let : FiniteDimensional B T := equalCharacteristicLubinTateLevelField_finiteDimensional F n
    SemilinearValuationCompatible B B' eB →
      eT (equalCharacteristicLubinTateArtinUnitToGal F n
          (equalCharacteristicLaurentPowerSeriesUnitPart F x)⁻¹ y) =
        Universe.abelianLocalArtinMonoidHom B' T' (Units.map eB.toMonoidHom x) (eT y) := by
  intro B T valuationOwner localFieldOwner finiteOwner hExt
  have h := Universe.abelianLocalArtinMonoidHom_semilinear_action
    B B' T T' eB eT hcomm hExt x y
  rw [equalCharacteristicAbelianLocalArtin_eq_explicitLaurentAction F n x] at h
  exact h

end LocalClassFieldTheory

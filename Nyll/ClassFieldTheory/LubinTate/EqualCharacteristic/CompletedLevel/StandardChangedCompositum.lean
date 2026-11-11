/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.StandardFrobeniusAction
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedNorm
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# The finite standard/changed compositum in equal characteristic

Inside the same completed level, take the compositum of the original
finite-level image and the changed Frobenius fixed field. Both factors
are finite over the Laurent base. The inverse completed Frobenius restricts
to an automorphism over the changed field and acts on the standard factor
by the direct unit bracket.

The construction keeps the existing chosen roots, theta value and Frobenius
lift. Identifying this relative automorphism with a native Artin value still
requires its unramified residue Frobenius normalization.
-/

@[expose] public section

noncomputable section

open scoped LaurentSeries PowerSeries

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

noncomputable local instance standardChangedCompositumBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  equalCharacteristicCompletedLevelBaseAlgebra F

noncomputable local instance standardChangedCompositumLevelAlgebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra F.residueField⸨X⸩ (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelLaurentAlgebra F n

/-- The original level's actual image in the completed level. -/
noncomputable def equalCharacteristicCompletedStandardLevelField
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic] (n : ℕ) :
    IntermediateField F.residueField⸨X⸩
      (equalCharacteristicCompletedLevelField F n) :=
  (equalCharacteristicLubinTateLevelFieldToCompleted F n).fieldRange

noncomputable instance equalCharacteristicCompletedStandardLevelField_finiteDimensional
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic] (n : ℕ) :
    FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicCompletedStandardLevelField F n) := by
  let : FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  exact (AlgEquiv.ofInjectiveField
    (equalCharacteristicLubinTateLevelFieldToCompleted F n)).toLinearEquiv.finiteDimensional

noncomputable instance equalCharacteristicCompletedFrobeniusFixedField_finiteDimensional
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicCompletedFrobeniusFixedField F a n) :=
  FiniteDimensional.of_finrank_pos (by
    rw [equalCharacteristicCompletedFrobeniusFixedField_finrank]
    exact Nat.mul_pos
      (Nat.sub_pos_of_lt (Finite.one_lt_card : 1 < Nat.card F.residueField))
      (Nat.pow_pos Nat.card_pos))

/-- The finite compositum of the original level and the changed fixed field. -/
noncomputable def equalCharacteristicCompletedStandardChangedCompositum
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    IntermediateField F.residueField⸨X⸩
      (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedStandardLevelField F n ⊔
    equalCharacteristicCompletedFrobeniusFixedField F a n

noncomputable instance equalCharacteristicCompletedStandardChangedCompositum_finiteDimensional
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicCompletedStandardChangedCompositum F a n) :=
  IntermediateField.finiteDimensional_sup
    (equalCharacteristicCompletedStandardLevelField F n)
    (equalCharacteristicCompletedFrobeniusFixedField F a n)

noncomputable instance equalCharacteristicCompletedStandardChangedCompositum_changedFieldAlgebra
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Algebra (equalCharacteristicCompletedFrobeniusFixedField F a n)
      (equalCharacteristicCompletedStandardChangedCompositum F a n) :=
  (IntermediateField.inclusion le_sup_right).toRingHom.toAlgebra

instance equalCharacteristicCompletedStandardChangedCompositum_changedFieldScalarTower
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    IsScalarTower F.residueField⸨X⸩
      (equalCharacteristicCompletedFrobeniusFixedField F a n)
      (equalCharacteristicCompletedStandardChangedCompositum F a n) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The original finite level embedded in the finite compositum. -/
noncomputable def equalCharacteristicStandardLevelToCompletedChangedCompositum
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicLubinTateLevelField F n →ₐ[F.residueField⸨X⸩]
      equalCharacteristicCompletedStandardChangedCompositum F a n :=
  (equalCharacteristicLubinTateLevelFieldToCompleted F n).codRestrict
    (equalCharacteristicCompletedStandardChangedCompositum F a n).toSubalgebra
    (fun x =>
      (show equalCharacteristicCompletedStandardLevelField F n ≤
          equalCharacteristicCompletedStandardChangedCompositum F a n from le_sup_left)
        (show equalCharacteristicLubinTateLevelFieldToCompleted F n x ∈
            equalCharacteristicCompletedStandardLevelField F n from ⟨x, rfl⟩))

/-- Inverse completed Frobenius preserves the standard finite image. -/
theorem equalCharacteristicCompletedFrobenius_symm_map_standard_le
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicCompletedStandardLevelField F n).map
        (equalCharacteristicCompletedFrobeniusAlgEquiv F a n).symm.toAlgHom ≤
      equalCharacteristicCompletedStandardLevelField F n := by
  rw [IntermediateField.map_le_iff_le_comap]
  intro x hx
  change x ∈ (equalCharacteristicLubinTateLevelFieldToCompleted F n).fieldRange at hx
  change (equalCharacteristicCompletedFrobeniusAlgEquiv F a n).symm x ∈
    (equalCharacteristicLubinTateLevelFieldToCompleted F n).fieldRange
  rw [AlgHom.mem_fieldRange] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨equalCharacteristicLubinTateArtinUnitToGal F n a⁻¹ y,
    (equalCharacteristicCompletedFrobeniusAlgEquiv_symm_levelFieldToCompleted
      F a n y).symm⟩

/-- Inverse Frobenius fixes the changed field pointwise. -/
theorem equalCharacteristicCompletedFrobenius_symm_fixed
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (x : equalCharacteristicCompletedFrobeniusFixedField F a n) :
    (equalCharacteristicCompletedFrobeniusAlgEquiv F a n).symm
        (x : equalCharacteristicCompletedLevelField F n) = x := by
  apply (equalCharacteristicCompletedFrobeniusAlgEquiv F a n).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (((IntermediateField.mem_fixedField_iff _ _).mp x.property)
    (equalCharacteristicCompletedFrobeniusAlgEquiv F a n)
    (Subgroup.mem_zpowers (equalCharacteristicCompletedFrobeniusAlgEquiv F a n))).symm

/-- Inverse Frobenius preserves the finite standard/changed compositum. -/
theorem equalCharacteristicCompletedFrobenius_symm_map_compositum_le
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicCompletedStandardChangedCompositum F a n).map
        (equalCharacteristicCompletedFrobeniusAlgEquiv F a n).symm.toAlgHom ≤
      equalCharacteristicCompletedStandardChangedCompositum F a n := by
  rw [equalCharacteristicCompletedStandardChangedCompositum, IntermediateField.map_sup]
  apply sup_le_sup (equalCharacteristicCompletedFrobenius_symm_map_standard_le F a n)
  rw [IntermediateField.map_le_iff_le_comap]
  intro x hx
  change (equalCharacteristicCompletedFrobeniusAlgEquiv F a n).symm x ∈
    equalCharacteristicCompletedFrobeniusFixedField F a n
  rw [equalCharacteristicCompletedFrobenius_symm_fixed F a n ⟨x, hx⟩]
  exact hx

/-- The inverse completed Frobenius restricted to the finite compositum. -/
noncomputable def equalCharacteristicCompletedStandardChangedInverseFrobeniusAlgHom
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicCompletedStandardChangedCompositum F a n →ₐ[F.residueField⸨X⸩]
      equalCharacteristicCompletedStandardChangedCompositum F a n :=
  ((equalCharacteristicCompletedFrobeniusAlgEquiv F a n).symm.toAlgHom.comp
      (equalCharacteristicCompletedStandardChangedCompositum F a n).val).codRestrict
    (equalCharacteristicCompletedStandardChangedCompositum F a n).toSubalgebra
    (fun x => by
      apply equalCharacteristicCompletedFrobenius_symm_map_compositum_le F a n
      rw [IntermediateField.mem_map]
      exact ⟨x, x.property, rfl⟩)

/-- The restricted inverse Frobenius is an automorphism of the finite compositum. -/
noncomputable def equalCharacteristicCompletedStandardChangedInverseFrobenius
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicCompletedStandardChangedCompositum F a n ≃ₐ[F.residueField⸨X⸩]
      equalCharacteristicCompletedStandardChangedCompositum F a n := by
  let f := equalCharacteristicCompletedStandardChangedInverseFrobeniusAlgHom F a n
  exact AlgEquiv.ofBijective f ⟨f.injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) rfl).mp f.injective⟩

/-- Its standard-factor value is the direct bracket, using the explicit
inverse-bracket homomorphism at the inverse unit. -/
theorem equalCharacteristicCompletedStandardChangedInverseFrobenius_standardLevel
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (x : equalCharacteristicLubinTateLevelField F n) :
    equalCharacteristicCompletedStandardChangedInverseFrobenius F a n
        (equalCharacteristicStandardLevelToCompletedChangedCompositum F a n x) =
      equalCharacteristicStandardLevelToCompletedChangedCompositum F a n
        (equalCharacteristicLubinTateArtinUnitToGal F n a⁻¹ x) := by
  apply Subtype.ext
  exact equalCharacteristicCompletedFrobeniusAlgEquiv_symm_levelFieldToCompleted F a n x

/-- The changed fixed field is fixed pointwise by the finite automorphism. -/
theorem equalCharacteristicCompletedStandardChangedInverseFrobenius_fixedField
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (x : equalCharacteristicCompletedFrobeniusFixedField F a n) :
    equalCharacteristicCompletedStandardChangedInverseFrobenius F a n
        (algebraMap (equalCharacteristicCompletedFrobeniusFixedField F a n)
          (equalCharacteristicCompletedStandardChangedCompositum F a n) x) =
      algebraMap (equalCharacteristicCompletedFrobeniusFixedField F a n)
        (equalCharacteristicCompletedStandardChangedCompositum F a n) x := by
  apply Subtype.ext
  exact equalCharacteristicCompletedFrobenius_symm_fixed F a n x

/-- The actual finite automorphism over the changed fixed field. -/
noncomputable def equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    equalCharacteristicCompletedStandardChangedCompositum F a n
      ≃ₐ[equalCharacteristicCompletedFrobeniusFixedField F a n]
        equalCharacteristicCompletedStandardChangedCompositum F a n where
  __ := (equalCharacteristicCompletedStandardChangedInverseFrobenius F a n).toRingEquiv
  commutes' := equalCharacteristicCompletedStandardChangedInverseFrobenius_fixedField F a n

end EqualCharacteristic
end LubinTate

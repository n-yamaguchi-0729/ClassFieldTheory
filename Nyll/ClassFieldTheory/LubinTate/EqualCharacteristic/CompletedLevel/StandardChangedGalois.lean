/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.StandardChangedCompositum
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

/-!
# The relative cyclic standard/changed extension

The relative inverse Frobenius has exactly the changed field as its fixed
field. Finite Galois correspondence therefore proves that it generates the
whole relative Galois group. This supplies the actual cyclic extension;
the valuation and residue-Frobenius comparison are separate statements.
-/

@[expose] public section

noncomputable section

open scoped LaurentSeries PowerSeries

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

noncomputable local instance standardChangedGaloisBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  equalCharacteristicCompletedLevelBaseAlgebra F

noncomputable local instance standardChangedGaloisLevelAlgebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra F.residueField⸨X⸩ (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelLaurentAlgebra F n

/-- The original finite image remains separable over the Laurent base. -/
instance equalCharacteristicCompletedStandardLevelField_isSeparable
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic] (n : ℕ) :
    Algebra.IsSeparable F.residueField⸨X⸩
      (equalCharacteristicCompletedStandardLevelField F n) :=
  Algebra.IsSeparable.of_algHom F.residueField⸨X⸩ (equalCharacteristicLubinTateLevelField F n)
    (AlgEquiv.ofInjectiveField
      (equalCharacteristicLubinTateLevelFieldToCompleted F n)).symm.toAlgHom

/-- The theta comparison identifies the changed fixed field with the
actual separable changed Lubin--Tate level. -/
instance equalCharacteristicCompletedFrobeniusFixedField_isSeparable
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Algebra.IsSeparable F.residueField⸨X⸩
      (equalCharacteristicCompletedFrobeniusFixedField F a n) :=
  Algebra.IsSeparable.of_algHom F.residueField⸨X⸩ (equalCharacteristicChangedLevelField F a n)
    (equalCharacteristicCompletedFrobeniusTargetLevelEquiv F a n).symm.toAlgHom

/-- Both factors, and therefore their actual compositum, are separable
over the Laurent base. -/
instance equalCharacteristicCompletedStandardChangedCompositum_isSeparable
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Algebra.IsSeparable F.residueField⸨X⸩
      (equalCharacteristicCompletedStandardChangedCompositum F a n) := by
  unfold equalCharacteristicCompletedStandardChangedCompositum
  infer_instance

/-- The same finite compositum is finite over its changed-field factor. -/
instance equalCharacteristicCompletedStandardChangedCompositum_relativeFiniteDimensional
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    FiniteDimensional (equalCharacteristicCompletedFrobeniusFixedField F a n)
      (equalCharacteristicCompletedStandardChangedCompositum F a n) :=
  FiniteDimensional.right F.residueField⸨X⸩
    (equalCharacteristicCompletedFrobeniusFixedField F a n)
    (equalCharacteristicCompletedStandardChangedCompositum F a n)

/-- The relative automorphism is the actual inverse completed Frobenius on
elements of the finite compositum. -/
theorem equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius_apply_coe
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (x : equalCharacteristicCompletedStandardChangedCompositum F a n) :
    ((equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius F a n x) :
        equalCharacteristicCompletedLevelField F n) =
      (equalCharacteristicCompletedFrobeniusAlgEquiv F a n).symm
        (x : equalCharacteristicCompletedLevelField F n) :=
  rfl

/-- Fixedness under the relative inverse Frobenius detects precisely the
actual changed-field factor in the completed ambient field. -/
theorem equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius_fixed_iff
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (x : equalCharacteristicCompletedStandardChangedCompositum F a n) :
    equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius F a n x = x ↔
      (x : equalCharacteristicCompletedLevelField F n) ∈
        equalCharacteristicCompletedFrobeniusFixedField F a n := by
  constructor
  · intro hx
    have hinv := congrArg Subtype.val hx
    rw [equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius_apply_coe]
      at hinv
    have hforward := congrArg (equalCharacteristicCompletedFrobeniusAlgEquiv F a n) hinv
    rw [AlgEquiv.apply_symm_apply] at hforward
    apply (IntermediateField.mem_fixedField_iff _ _).mpr
    intro σ hσ
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ
    have hfixed : (x : equalCharacteristicCompletedLevelField F n) ∈
        MulAction.fixedBy (equalCharacteristicCompletedLevelField F n)
          (equalCharacteristicCompletedFrobeniusAlgEquiv F a n) :=
      MulAction.mem_fixedBy.mpr hforward.symm
    exact MulAction.mem_fixedBy.mp (MulAction.mem_fixedBy_zpow hfixed j)
  · intro hx
    apply Subtype.ext
    rw [equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius_apply_coe]
    exact equalCharacteristicCompletedFrobenius_symm_fixed F a n ⟨x, hx⟩

/-- The cyclic subgroup generated by the relative inverse Frobenius has no
fixed elements beyond the relative base field. -/
theorem equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius_fixedField
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    IntermediateField.fixedField
        (Subgroup.zpowers
          (equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius F a n)) =
      ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  have hσ := ((IntermediateField.mem_fixedField_iff _ _).mp hx)
    (equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius F a n)
    (Subgroup.mem_zpowers
      (equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius F a n))
  have hxD :=
    (equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius_fixed_iff
      F a n x).mp hσ
  apply IntermediateField.mem_bot.mpr
  refine ⟨⟨(x : equalCharacteristicCompletedLevelField F n), hxD⟩, ?_⟩
  apply Subtype.ext
  rfl

/-- The specified relative inverse Frobenius generates the actual relative
automorphism group of the finite compositum. -/
theorem equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius_zpowers_eq_top
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    Subgroup.zpowers
        (equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius F a n) =
      ⊤ := by
  rw [← IntermediateField.fixingSubgroup_fixedField
      (Subgroup.zpowers
        (equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius F a n)),
    equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius_fixedField,
    IntermediateField.fixingSubgroup_bot]

/-- The standard/changed compositum is Galois over the changed field. -/
instance equalCharacteristicCompletedStandardChangedCompositum_relativeIsGalois
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    IsGalois (equalCharacteristicCompletedFrobeniusFixedField F a n)
      (equalCharacteristicCompletedStandardChangedCompositum F a n) := by
  apply IsGalois.of_fixedField_eq_bot
  rw [← equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius_zpowers_eq_top
    F a n]
  exact equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius_fixedField F a n

/-- The relative Galois group is cyclic, with its generator supplied by the
actual inverse completed Frobenius. -/
instance equalCharacteristicCompletedStandardChangedCompositum_relativeIsCyclic
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    IsCyclic
      (Gal((equalCharacteristicCompletedStandardChangedCompositum F a n) /
        (equalCharacteristicCompletedFrobeniusFixedField F a n))) :=
  isCyclic_iff_exists_zpowers_eq_top.mpr
    ⟨equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius F a n,
      equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius_zpowers_eq_top F a n⟩

/-- The concrete relative extension is abelian Galois. -/
instance equalCharacteristicCompletedStandardChangedCompositum_relativeIsAbelianGalois
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    IsAbelianGalois (equalCharacteristicCompletedFrobeniusFixedField F a n)
      (equalCharacteristicCompletedStandardChangedCompositum F a n) where
  toIsGalois := equalCharacteristicCompletedStandardChangedCompositum_relativeIsGalois F a n
  toIsMulCommutative := inferInstance

end EqualCharacteristic
end LubinTate

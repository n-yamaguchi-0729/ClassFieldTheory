/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.UnitQuotientGalois
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedField
public import Mathlib.GroupTheory.GroupAction.FixedPoints

/-!
# The completed Frobenius action on the original finite level

The chosen embedding sends the original primitive point to the completed
primitive point. Polynomial evaluation then identifies the restriction of
the completed arithmetic Frobenius lift with the explicit inverse-unit
action. Its inverse restricts to the direct-unit action.

These are pointwise statements about the actual embedding and automorphisms.
They do not identify the explicit action with the native local Artin map;
that comparison also requires the relative unramified Frobenius calculation.
-/

@[expose] public section

noncomputable section

open scoped LaurentSeries PowerSeries Polynomial

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

noncomputable local instance standardFrobeniusActionBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  equalCharacteristicCompletedLevelBaseAlgebra F

noncomputable local instance standardFrobeniusActionLevelAlgebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra F.residueField⸨X⸩ (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelLaurentAlgebra F n

/-- The actual finite-level embedding respects every truncated bracket. -/
theorem equalCharacteristicLubinTateLevelFieldToCompleted_bracket
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (n m : ℕ) (a : F.residueField⟦X⟧)
    (x : equalCharacteristicLubinTateLevelField F n) :
    equalCharacteristicLubinTateLevelFieldToCompleted F n
        (equalCharacteristicLubinTateLevelBracket F n m a x) =
      equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicCompletedLevelResidueHom F n)
        (equalCharacteristicCompletedLevelUniformizer F n) m a
        (equalCharacteristicLubinTateLevelFieldToCompleted F n x) := by
  rw [equalCharacteristicLubinTateLevelBracket_eq_aeval,
    ← Polynomial.aeval_algHom_apply]
  change Polynomial.eval₂ (equalCharacteristicCompletedLevelBaseHom F n)
      (equalCharacteristicLubinTateLevelFieldToCompleted F n x)
      (equalCharacteristicLubinTateBracketPolynomial F m a) = _
  rw [equalCharacteristicLubinTateBracketPolynomial_eval₂,
    equalCharacteristicCompletedLevelBaseHom_uniformizer]
  rfl

/-- The chosen original and completed primitive generators agree under the
actual level embedding. -/
@[simp]
theorem equalCharacteristicLubinTateLevelFieldToCompleted_powerBasis_gen
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic] (n : ℕ) :
    equalCharacteristicLubinTateLevelFieldToCompleted F n
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
      equalCharacteristicCompletedPrimitiveRoot F n := by
  rw [equalCharacteristicLubinTateLevelPowerBasis,
    IntermediateField.adjoin.powerBasis_gen,
    equalCharacteristicLubinTateLevelFieldToCompleted_generator]

/-- The arithmetic completed lift restricts pointwise to the explicit
inverse-unit action on the original finite level. -/
theorem equalCharacteristicCompletedFrobeniusAlgEquiv_levelFieldToCompleted
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (x : equalCharacteristicLubinTateLevelField F n) :
    equalCharacteristicCompletedFrobeniusAlgEquiv F a n
        (equalCharacteristicLubinTateLevelFieldToCompleted F n x) =
      equalCharacteristicLubinTateLevelFieldToCompleted F n
        (equalCharacteristicLubinTateArtinUnitToGal F n a x) := by
  have h :
      (equalCharacteristicCompletedFrobeniusAlgEquiv F a n).toAlgHom.comp
          (equalCharacteristicLubinTateLevelFieldToCompleted F n) =
        (equalCharacteristicLubinTateLevelFieldToCompleted F n).comp
          (equalCharacteristicLubinTateArtinUnitToGal F n a).toAlgHom := by
    apply (equalCharacteristicLubinTateLevelPowerBasis F n).algHom_ext
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
      equalCharacteristicLubinTateLevelFieldToCompleted_powerBasis_gen,
      equalCharacteristicCompletedFrobeniusAlgEquiv_apply,
      equalCharacteristicCompletedFrobeniusLiftEquiv_primitiveRoot,
      equalCharacteristicLubinTateArtinUnitToGal_apply_gen]
    rw [equalCharacteristicLubinTateArtinUnitLevelRoot,
      equalCharacteristicLubinTateLevelFieldToCompleted_bracket,
      equalCharacteristicLubinTateLevelFieldToCompleted_powerBasis_gen]
    rfl
  exact DFunLike.congr_fun h x

/-- The inverse completed lift restricts to `[a]`, expressed using the
existing inverse-unit action at `a⁻¹`. This fixes the orientation without
changing either automorphism's definition. -/
theorem equalCharacteristicCompletedFrobeniusAlgEquiv_symm_levelFieldToCompleted
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (x : equalCharacteristicLubinTateLevelField F n) :
    (equalCharacteristicCompletedFrobeniusAlgEquiv F a n).symm
        (equalCharacteristicLubinTateLevelFieldToCompleted F n x) =
      equalCharacteristicLubinTateLevelFieldToCompleted F n
        (equalCharacteristicLubinTateArtinUnitToGal F n a⁻¹ x) := by
  apply (equalCharacteristicCompletedFrobeniusAlgEquiv F a n).injective
  rw [AlgEquiv.apply_symm_apply,
    equalCharacteristicCompletedFrobeniusAlgEquiv_levelFieldToCompleted,
    map_inv]
  exact congrArg (equalCharacteristicLubinTateLevelFieldToCompleted F n)
    ((equalCharacteristicLubinTateArtinUnitToGal F n a).apply_symm_apply x).symm

/-- Belonging to the changed Frobenius fixed field is exactly fixedness
under the explicit inverse-unit action, on the actual finite-level image. -/
theorem equalCharacteristicLubinTateLevelFieldToCompleted_mem_fixedField_iff
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (x : equalCharacteristicLubinTateLevelField F n) :
    equalCharacteristicLubinTateLevelFieldToCompleted F n x ∈
        equalCharacteristicCompletedFrobeniusFixedField F a n ↔
      equalCharacteristicLubinTateArtinUnitToGal F n a x = x := by
  constructor
  · intro hx
    have hfixed := ((IntermediateField.mem_fixedField_iff _ _).mp hx)
      (equalCharacteristicCompletedFrobeniusAlgEquiv F a n)
      (Subgroup.mem_zpowers (equalCharacteristicCompletedFrobeniusAlgEquiv F a n))
    apply (equalCharacteristicLubinTateLevelFieldToCompleted F n).injective
    exact
      (equalCharacteristicCompletedFrobeniusAlgEquiv_levelFieldToCompleted
        F a n x).symm.trans hfixed
  · intro hx
    apply (IntermediateField.mem_fixedField_iff _ _).mpr
    intro σ hσ
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ
    have hfixed : equalCharacteristicLubinTateLevelFieldToCompleted F n x ∈
        MulAction.fixedBy (equalCharacteristicCompletedLevelField F n)
          (equalCharacteristicCompletedFrobeniusAlgEquiv F a n) := by
      rw [MulAction.mem_fixedBy]
      change equalCharacteristicCompletedFrobeniusAlgEquiv F a n
          (equalCharacteristicLubinTateLevelFieldToCompleted F n x) = _
      rw [equalCharacteristicCompletedFrobeniusAlgEquiv_levelFieldToCompleted, hx]
    exact MulAction.mem_fixedBy.mp (MulAction.mem_fixedBy_zpow hfixed j)

end EqualCharacteristic
end LubinTate

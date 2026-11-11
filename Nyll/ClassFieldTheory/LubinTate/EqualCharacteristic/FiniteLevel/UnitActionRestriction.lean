/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.UnitQuotientGalois
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FreeRankOne
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAbelian
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAutomorphisms
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelFieldTower
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.AmbientBracketAction
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction

/-!
# Restriction of the explicit Lubin--Tate unit action

The inverse-bracket action is compatible with the actual inclusions of the
finite level fields. The primitive roots at different levels need not have
been chosen compatibly: the proof first computes the action on every torsion
point, then applies that computation to the lower-level primitive root.

These are statements about the explicit action. They do not identify it with
the native local Artin map or choose a Frobenius normalization for that map.
-/

@[expose] public section

noncomputable section

open scoped LaurentSeries PowerSeries

universe u v w

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LubinTate.EqualCharacteristic

variable {K : Type u} [Field K]

/-- A bracket on a torsion point is unchanged when its truncation level is
increased beyond the torsion level. -/
theorem equalCharacteristicLubinTateAmbientBracket_eq_of_torsion_of_le
    (F : LocalField.{u, v} K)
    {A : Type w} [Field A] [CharP A F.residueCharacteristic]
    (ι : F.residueField →+* A) (t : A)
    {m n : ℕ} (hmn : m ≤ n) (a : F.residueField⟦X⟧) (x : A)
    (hx : IsEqualCharacteristicLubinTateAmbientTorsion F t m x) :
    equalCharacteristicLubinTateAmbientBracket F ι t n a x =
      equalCharacteristicLubinTateAmbientBracket F ι t m a x := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      rw [equalCharacteristicLubinTateAmbientBracket_succ_eq_of_torsion
        F ι t n a x
        (equalCharacteristicLubinTateAmbientPiIterate_eq_zero_of_le
          F t hmn x hx)]
      exact ih

/-- The explicit inverse-bracket automorphism has the same formula on every
division point in the level field, not only on its chosen generator. -/
theorem equalCharacteristicLubinTateArtinUnitToGal_apply_of_torsion
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ)
    (x : equalCharacteristicLubinTateLevelField F n)
    (hx : IsEqualCharacteristicLubinTateAmbientTorsion F
      (equalCharacteristicSeparableUniformizer F) (n + 1)
      (x : SeparableClosure F.residueField⸨X⸩)) :
    equalCharacteristicLubinTateArtinUnitToGal F n a x =
      equalCharacteristicLubinTateLevelBracket F n (n + 1)
        ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧) x := by
  obtain ⟨p, hp⟩ :=
    (equalCharacteristicLubinTateParameterRoot_bijective F n).surjective
      ⟨(x : SeparableClosure F.residueField⸨X⸩), hx⟩
  let b := equalCharacteristicLubinTateParameterSeries F n p
  have hxb :
      equalCharacteristicLubinTateLevelBracket F n (n + 1) b
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen = x := by
    apply Subtype.ext
    exact congrArg (fun z : equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
      (equalCharacteristicSeparableUniformizer F) (n + 1) =>
        (z : SeparableClosure F.residueField⸨X⸩)) hp
  rw [← hxb]
  have hmap := equalCharacteristicLubinTateLevelBracket_map F n (n + 1) b
    (equalCharacteristicLubinTateArtinUnitToGal F n a).toAlgHom
    (equalCharacteristicLubinTateLevelPowerBasis F n).gen
  rw [show equalCharacteristicLubinTateArtinUnitToGal F n a
      (equalCharacteristicLubinTateLevelBracket F n (n + 1) b
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen) =
      equalCharacteristicLubinTateLevelBracket F n (n + 1) b
        (equalCharacteristicLubinTateArtinUnitToGal F n a
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen) from hmap,
    equalCharacteristicLubinTateArtinUnitToGal_apply_gen]
  apply Subtype.ext
  change
    equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1) b
        (equalCharacteristicLubinTateAmbientBracket F
          (equalCharacteristicSeparableCoefficientHom F)
          (equalCharacteristicSeparableUniformizer F) (n + 1)
          ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
          (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)) =
      equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
        (equalCharacteristicLubinTateAmbientBracket F
          (equalCharacteristicSeparableCoefficientHom F)
          (equalCharacteristicSeparableUniformizer F) (n + 1) b
          (chosenEqualCharacteristicLubinTatePrimitiveRoot F n))
  rw [← equalCharacteristicLubinTateAmbientBracket_mul_apply_of_torsion
      F (equalCharacteristicSeparableCoefficientHom F)
      (equalCharacteristicSeparableUniformizer F) (n + 1) b
      ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
      (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
      (chosenEqualCharacteristicLubinTatePrimitiveRoot_torsion F n),
    ← equalCharacteristicLubinTateAmbientBracket_mul_apply_of_torsion
      F (equalCharacteristicSeparableCoefficientHom F)
      (equalCharacteristicSeparableUniformizer F) (n + 1)
      ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧) b
      (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
      (chosenEqualCharacteristicLubinTatePrimitiveRoot_torsion F n),
    mul_comm b]

/-- The actual inclusion of two Lubin--Tate levels intertwines the explicit
unit actions, independently of the choices of primitive roots. -/
theorem equalCharacteristicLubinTateArtinUnitToGal_inclusion
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {m n : ℕ} (hmn : m ≤ n) (a : F.residueField⟦X⟧ˣ) :
    (equalCharacteristicLubinTateArtinUnitToGal F n a).toAlgHom.comp
        (IntermediateField.inclusion
          (equalCharacteristicLubinTateLevelField_mono F hmn)) =
      (IntermediateField.inclusion
          (equalCharacteristicLubinTateLevelField_mono F hmn)).comp
        (equalCharacteristicLubinTateArtinUnitToGal F m a).toAlgHom := by
  apply (equalCharacteristicLubinTateLevelPowerBasis F m).algHom_ext
  change equalCharacteristicLubinTateArtinUnitToGal F n a
      (IntermediateField.inclusion
        (equalCharacteristicLubinTateLevelField_mono F hmn)
        (equalCharacteristicLubinTateLevelPowerBasis F m).gen) =
    IntermediateField.inclusion
      (equalCharacteristicLubinTateLevelField_mono F hmn)
      (equalCharacteristicLubinTateArtinUnitToGal F m a
        (equalCharacteristicLubinTateLevelPowerBasis F m).gen)
  let gen := IntermediateField.inclusion (equalCharacteristicLubinTateLevelField_mono F hmn)
    (equalCharacteristicLubinTateLevelPowerBasis F m).gen
  have hgen : IsEqualCharacteristicLubinTateAmbientTorsion F
      (equalCharacteristicSeparableUniformizer F) (n + 1)
      (gen : SeparableClosure F.residueField⸨X⸩) := by
    change equalCharacteristicLubinTateAmbientPiIterate F
      (equalCharacteristicSeparableUniformizer F) (n + 1)
      (chosenEqualCharacteristicLubinTatePrimitiveRoot F m) = 0
    exact equalCharacteristicLubinTateAmbientPiIterate_eq_zero_of_le F
      (equalCharacteristicSeparableUniformizer F) (Nat.succ_le_succ hmn)
      (chosenEqualCharacteristicLubinTatePrimitiveRoot F m)
      (chosenEqualCharacteristicLubinTatePrimitiveRoot_torsion F m)
  rw [equalCharacteristicLubinTateArtinUnitToGal_apply_of_torsion F n a gen hgen,
    equalCharacteristicLubinTateArtinUnitToGal_apply_gen]
  apply Subtype.ext
  exact equalCharacteristicLubinTateAmbientBracket_eq_of_torsion_of_le F
    (equalCharacteristicSeparableCoefficientHom F)
    (equalCharacteristicSeparableUniformizer F) (Nat.succ_le_succ hmn)
    ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
    (chosenEqualCharacteristicLubinTatePrimitiveRoot F m)
    (chosenEqualCharacteristicLubinTatePrimitiveRoot_torsion F m)

/-- Restricting the explicit finite-level unit automorphism gives the same
unit automorphism on every lower level. -/
theorem equalCharacteristicLubinTateArtinUnitToGal_restrict
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    {m n : ℕ} (hmn : m ≤ n) (a : F.residueField⟦X⟧ˣ) :
    RamificationTheory.intermediateFieldRestrictNormalHom
        (equalCharacteristicLubinTateLevelField F m)
        (equalCharacteristicLubinTateLevelField F n)
        (equalCharacteristicLubinTateLevelField_mono F hmn)
        (equalCharacteristicLubinTateArtinUnitToGal F n a) =
      equalCharacteristicLubinTateArtinUnitToGal F m a := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  change (equalCharacteristicLubinTateLevelField F m).val
      (RamificationTheory.intermediateFieldRestrictNormalHom
        (equalCharacteristicLubinTateLevelField F m)
        (equalCharacteristicLubinTateLevelField F n)
        (equalCharacteristicLubinTateLevelField_mono F hmn)
        (equalCharacteristicLubinTateArtinUnitToGal F n a) x) =
    (equalCharacteristicLubinTateLevelField F m).val
      (equalCharacteristicLubinTateArtinUnitToGal F m a x)
  rw [RamificationTheory.intermediateFieldRestrictNormalHom_apply_val]
  exact congrArg Subtype.val
    (DFunLike.congr_fun
      (equalCharacteristicLubinTateArtinUnitToGal_inclusion F hmn a) x)

/-- Inverting the input unit in the existing inverse-bracket action gives
the direct bracket on the chosen primitive point. -/
theorem equalCharacteristicLubinTateArtinUnitToGal_inv_apply_gen_coe
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    ((equalCharacteristicLubinTateArtinUnitToGal F n a⁻¹)
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen :
        SeparableClosure F.residueField⸨X⸩) =
      equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        (a : F.residueField⟦X⟧)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) := by
  rw [equalCharacteristicLubinTateArtinUnitToGal_apply_gen]
  change equalCharacteristicLubinTateAmbientBracket F
      (equalCharacteristicSeparableCoefficientHom F)
      (equalCharacteristicSeparableUniformizer F) (n + 1)
      (((a⁻¹)⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
      (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) = _
  rw [inv_inv]

end LubinTate

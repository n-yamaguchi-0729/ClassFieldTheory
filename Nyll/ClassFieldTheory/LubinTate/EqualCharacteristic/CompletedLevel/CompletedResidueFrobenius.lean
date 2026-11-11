/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusIntegers
public import Nyll.ValuedFieldTheory.Valuation.FiniteResidueExtension
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Degree
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Residue Frobenius on the completed equal-characteristic level

The coefficient field has residue field the algebraic closure of the finite
coefficient field. Its finite completed-level extension therefore has the
same residue field. Under the actual residue inclusion, the integer
Frobenius lift induces the cardinality-power Frobenius on every residue.
-/

@[expose] public section

noncomputable section

open scoped LaurentSeries PowerSeries

universe u v w

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ResidueField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} [Field K]

/-- Reduction of the native Laurent valuation ring is reduction of power
series to their constant coefficient. -/
noncomputable def equalCharacteristicCompletedUnramifiedResidueFieldEquiv
    (k : Type w) [Field k] :
    (equalCharacteristicCompletedUnramifiedCompleteDVF k).residueField ≃+*
      AlgebraicClosure k :=
  (IsLocalRing.ResidueField.mapEquiv
      (powerSeriesEquivLaurentInteger (AlgebraicClosure k))).symm.trans
    PowerSeries.residueFieldOfPowerSeries

/-- The actual coefficient residue field is algebraically closed. -/
theorem equalCharacteristicCompletedUnramifiedResidueField_isAlgClosed
    (k : Type w) [Field k] :
    IsAlgClosed (equalCharacteristicCompletedUnramifiedCompleteDVF k).residueField :=
  IsAlgClosed.of_ringEquiv (AlgebraicClosure k)
    (equalCharacteristicCompletedUnramifiedCompleteDVF k).residueField
    (equalCharacteristicCompletedUnramifiedResidueFieldEquiv k).symm

/-- A finite extension of the completed coefficient field cannot enlarge
its already algebraically closed residue field. -/
theorem equalCharacteristicCompletedLevel_residueMap_surjective
    (F : LocalField.{u, v} K) (n : ℕ) :
    Function.Surjective
      (residueMap
        (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).toDVF
        (equalCharacteristicCompletedLevelCompleteDVF F n).toDVF) := by
  let base := equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField
  let target := equalCharacteristicCompletedLevelCompleteDVF F n
  let : IsAlgClosed base.residueField :=
    equalCharacteristicCompletedUnramifiedResidueField_isAlgClosed F.residueField
  let : FiniteDimensional base.residueField target.residueField :=
    Valuation.finiteDimensional_residueField base.valuation target.valuation
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := base.residueField) (K := target.residueField)).2

/-- The actual residue inclusion has linear degree one. -/
theorem equalCharacteristicCompletedLevel_residueField_finrank_eq_one
    (F : LocalField.{u, v} K) (n : ℕ) :
    Module.finrank
        (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).residueField
        (equalCharacteristicCompletedLevelCompleteDVF F n).residueField = 1 := by
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
  exact ⟨residueMap_injective
      (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).toDVF
      (equalCharacteristicCompletedLevelCompleteDVF F n).toDVF,
    equalCharacteristicCompletedLevel_residueMap_surjective F n⟩

/-- The completed level has residue degree one over its coefficient field. -/
theorem equalCharacteristicCompletedLevel_residueDegree_eq_one
    (F : LocalField.{u, v} K) (n : ℕ) :
    residueDegree
        (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).toDVF
        (equalCharacteristicCompletedLevelCompleteDVF F n).toDVF = 1 := by
  let base := equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField
  let target := equalCharacteristicCompletedLevelCompleteDVF F n
  let E := equalCharacteristicCompletedLevelField F n
  let : IsScalarTower base.valuationSubring target.valuationSubring E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : target.maximalIdeal.LiesOver base.maximalIdeal :=
    maximalIdeal_liesOver base target
  rw [residueDegree_eq_finrank_quotient base target]
  exact equalCharacteristicCompletedLevel_residueField_finrank_eq_one F n

/-- The completed-level residue equivalence is the actual residue map. -/
noncomputable def equalCharacteristicCompletedLevelResidueFieldEquiv
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).residueField ≃+*
      (equalCharacteristicCompletedLevelCompleteDVF F n).residueField :=
  residueFieldEquivOfSurjective
    (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).toDVF
    (equalCharacteristicCompletedLevelCompleteDVF F n).toDVF
    (equalCharacteristicCompletedLevel_residueMap_surjective F n)

/-- Integral representatives reduce through the same actual inclusion. -/
@[simp]
theorem equalCharacteristicCompletedLevelResidueFieldEquiv_apply_residue
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).valuationSubring) :
    equalCharacteristicCompletedLevelResidueFieldEquiv F n
        ((equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).residueMap a) =
      (equalCharacteristicCompletedLevelCompleteDVF F n).residueMap
        (integerMap
          (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).toDVF
          (equalCharacteristicCompletedLevelCompleteDVF F n).toDVF a) :=
  residueFieldEquivOfSurjective_apply_residue
    (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).toDVF
    (equalCharacteristicCompletedLevelCompleteDVF F n).toDVF
    (equalCharacteristicCompletedLevel_residueMap_surjective F n) a

private theorem equalCharacteristicPowerSeries_residue_frobenius_eq_pow
    (k : Type w) [Field k] [Finite k] (f : (AlgebraicClosure k)⟦X⟧) :
    IsLocalRing.residue ((AlgebraicClosure k)⟦X⟧)
        (equalCharacteristicPowerSeriesFrobenius k f) =
      IsLocalRing.residue ((AlgebraicClosure k)⟦X⟧) f ^ Nat.card k := by
  rw [← map_pow, residue_eq_residue_iff_sub_mem_maximalIdeal,
    ← PowerSeries.ker_coeff_eq_max_ideal, RingHom.mem_ker, map_sub, map_pow]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    equalCharacteristicPowerSeriesFrobenius_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, sub_self]

/-- Every unit-indexed completed Frobenius lift induces the arithmetic
`card(k)`-power action on the actual completed-level residue field. -/
theorem equalCharacteristicCompletedFrobeniusIntegerEquiv_residue_apply_eq_pow
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ)
    (x : (equalCharacteristicCompletedLevelCompleteDVF F n).residueField) :
    IsLocalRing.ResidueField.mapEquiv
        (equalCharacteristicCompletedFrobeniusIntegerEquiv F n a) x =
      x ^ Nat.card F.residueField := by
  let W := (AlgebraicClosure F.residueField)⟦X⟧
  let base := equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField
  let target := equalCharacteristicCompletedLevelCompleteDVF F n
  let e : W ≃+* base.valuationSubring :=
    powerSeriesEquivLaurentInteger (AlgebraicClosure F.residueField)
  let residueEquiv : IsLocalRing.ResidueField W ≃+* target.residueField :=
    (IsLocalRing.ResidueField.mapEquiv e).trans
      (equalCharacteristicCompletedLevelResidueFieldEquiv F n)
  have hcoefficient (f : W) :
      residueEquiv (IsLocalRing.residue W f) =
        target.residueMap (integerMap base.toDVF target.toDVF (e f)) := by
    simp only [residueEquiv, RingEquiv.trans_apply,
      IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    exact equalCharacteristicCompletedLevelResidueFieldEquiv_apply_residue F n (e f)
  obtain ⟨z, rfl⟩ := residueEquiv.surjective x
  obtain ⟨f, rfl⟩ := IsLocalRing.residue_surjective z
  calc
    IsLocalRing.ResidueField.mapEquiv
        (equalCharacteristicCompletedFrobeniusIntegerEquiv F n a)
        (residueEquiv (IsLocalRing.residue W f)) =
      target.residueMap
        (equalCharacteristicCompletedFrobeniusIntegerEquiv F n a
          (integerMap base.toDVF target.toDVF (e f))) := by
            rw [hcoefficient]
            rfl
    _ = target.residueMap
        (integerMap base.toDVF target.toDVF
          (e (equalCharacteristicPowerSeriesFrobenius F.residueField f))) := by
            rw [equalCharacteristicCompletedFrobeniusIntegerEquiv_integerMap]
            exact congrArg (fun z : base.valuationSubring =>
              target.residueMap (integerMap base.toDVF target.toDVF z))
              (equalCharacteristicCompletedUnramifiedFrobeniusIntegerEquiv_powerSeries
                F.residueField f)
    _ = residueEquiv
        (IsLocalRing.residue W
          (equalCharacteristicPowerSeriesFrobenius F.residueField f)) :=
      (hcoefficient (equalCharacteristicPowerSeriesFrobenius F.residueField f)).symm
    _ = residueEquiv (IsLocalRing.residue W f ^ Nat.card F.residueField) := by
      rw [equalCharacteristicPowerSeries_residue_frobenius_eq_pow]
    _ = residueEquiv (IsLocalRing.residue W f) ^ Nat.card F.residueField := by
      rw [map_pow]

end EqualCharacteristic
end LubinTate

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompleteValuations
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveAction
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveIrreducible
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedCompletedPrimitiveAction
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldPrimitive
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentLocalField
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.NormUniformizer
public import Mathlib.Algebra.Group.Irreducible.Lemmas

/-!
# Actual uniformizers of the completed equal-characteristic level

The constant coefficients of the primitive minimal polynomials are a unit
times the Laurent parameter. The norm formula and the fundamental
ramification identity therefore prove that their actual roots are
uniformizers for the selected integral-closure valuation.
-/

@[expose] public section

noncomputable section
open scoped LaurentSeries PowerSeries BigOperators

namespace LubinTate.EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.ValuedExtension
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open RamificationTheory.HilbertRamification.Higher

universe u v w x

variable {K : Type u} [Field K]

private theorem completedPrimitive_of_integralPolynomial
    (F : LocalField.{u, v} K) (n : ℕ)
    (B : PowerBasis (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n))
    (P : Polynomial (AlgebraicClosure F.residueField)⟦X⟧)
    (hmonic : P.Monic)
    (hmap : P.map (algebraMap (AlgebraicClosure F.residueField)⟦X⟧
        (equalCharacteristicCompletedUnramifiedField F.residueField)) =
      minpoly (equalCharacteristicCompletedUnramifiedField F.residueField) B.gen)
    (hcoeff : Irreducible (P.coeff 0)) :
    (equalCharacteristicCompletedLevelCompleteDVF F n).valuation.IsUniformizer B.gen ∧
      ramificationIndex (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).toDVF
          (equalCharacteristicCompletedLevelCompleteDVF F n).toDVF =
        degree (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).toDVF
          (equalCharacteristicCompletedLevelCompleteDVF F n).toDVF := by
  let base := equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField
  let target := equalCharacteristicCompletedLevelCompleteDVF F n
  let e : (AlgebraicClosure F.residueField)⟦X⟧ ≃+* base.valuationSubring :=
    powerSeriesEquivLaurentInteger (AlgebraicClosure F.residueField)
  let : IsIntegralClosure target.valuationSubring base.valuationSubring
      (equalCharacteristicCompletedLevelField F n) :=
    equalCharacteristicCompletedLevelCompleteDVF_isIntegralClosure F n
  apply isUniformizer_and_ramificationIndex_eq_degree_of_integral_minpoly
    base target B (P.map e.toRingHom) (hmonic.map e.toRingHom)
  · have hcomp : (algebraMap base.valuationSubring
          (equalCharacteristicCompletedUnramifiedField F.residueField)).comp e.toRingHom =
        algebraMap (AlgebraicClosure F.residueField)⟦X⟧
          (equalCharacteristicCompletedUnramifiedField F.residueField) := by
      ext f
      rfl
    rw [Polynomial.map_map, hcomp]
    exact hmap
  · rw [Polynomial.coeff_map]
    exact hcoeff.map e

/-- The standard completed primitive root is a uniformizer of the actual
integral-closure valuation. -/
theorem equalCharacteristicCompletedPrimitiveRoot_isUniformizer
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic] (n : ℕ) :
    (equalCharacteristicCompletedLevelCompleteDVF F n).valuation.IsUniformizer
      (equalCharacteristicCompletedPrimitiveRoot F n) := by
  have h := completedPrimitive_of_integralPolynomial F n
    (equalCharacteristicCompletedPrimitivePowerBasis F n)
    (equalCharacteristicCompletedIntegralPrimitivePolynomial F n)
    (equalCharacteristicCompletedIntegralPrimitivePolynomial_monic F n)
    (by rw [equalCharacteristicCompletedIntegralPrimitivePolynomial_map,
      equalCharacteristicCompletedPrimitivePowerBasis_gen,
      equalCharacteristicCompletedPrimitiveRoot_minpoly])
    (by rw [equalCharacteristicCompletedIntegralPrimitivePolynomial_coeff_zero]
        exact PowerSeries.X_irreducible)
  simpa only [equalCharacteristicCompletedPrimitivePowerBasis_gen] using h.1

/-- The actual completed primitive level is totally ramified over its
completed coefficient field. -/
theorem equalCharacteristicCompletedLevel_ramificationIndex_eq_degree
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic] (n : ℕ) :
    ramificationIndex (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).toDVF
        (equalCharacteristicCompletedLevelCompleteDVF F n).toDVF =
      degree (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).toDVF
        (equalCharacteristicCompletedLevelCompleteDVF F n).toDVF := by
  exact (completedPrimitive_of_integralPolynomial F n
    (equalCharacteristicCompletedPrimitivePowerBasis F n)
    (equalCharacteristicCompletedIntegralPrimitivePolynomial F n)
    (equalCharacteristicCompletedIntegralPrimitivePolynomial_monic F n)
    (by rw [equalCharacteristicCompletedIntegralPrimitivePolynomial_map,
      equalCharacteristicCompletedPrimitivePowerBasis_gen,
      equalCharacteristicCompletedPrimitiveRoot_minpoly])
    (by rw [equalCharacteristicCompletedIntegralPrimitivePolynomial_coeff_zero]
        exact PowerSeries.X_irreducible)).2

/-- The genuine direct theta value is a uniformizer for the same selected
completed-level valuation. Its changed minimal polynomial has constant
coefficient a unit times the Laurent parameter. -/
theorem equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_isUniformizer
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    (equalCharacteristicCompletedLevelCompleteDVF F n).valuation.IsUniformizer
      (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n :
        equalCharacteristicCompletedLevelField F n) := by
  have hIntegral :=
    equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_isIntegral_completedBase F a n
  have hAdjoin := Algebra.adjoin_eq_top_of_primitive_element hIntegral.isAlgebraic
    (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_adjoin_completedBase_eq_top F a n)
  let B := PowerBasis.ofAdjoinEqTop hIntegral hAdjoin
  have hgen : B.gen = (equalCharacteristicDirectThetaAtCompletedPrimitiveRoot F a n :
      equalCharacteristicCompletedLevelField F n) :=
    PowerBasis.ofAdjoinEqTop_gen _ _
  have h := completedPrimitive_of_integralPolynomial F n B
    (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial F a⁻¹ n)
    (equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_monic F a⁻¹ n)
    (by rw [equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_map,
      hgen, equalCharacteristicDirectThetaAtCompletedPrimitiveRoot_minpoly_completedBase])
    (by
      rw [equalCharacteristicChangedCompletedIntegralPrimitivePolynomial_coeff_zero]
      exact (irreducible_isUnit_mul
        (equalCharacteristicChangedCompletedSourceUnit F a⁻¹).isUnit).mpr
          PowerSeries.X_irreducible)
  rw [hgen] at h
  exact h.1

end LubinTate.EqualCharacteristic

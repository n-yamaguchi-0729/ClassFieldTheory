/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Localization.NormTrace
public import Nyll.SchemeTheory.RingTheory.NormCongruence
public import Nyll.SchemeTheory.RingTheory.NormIdentities
public import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.LocalRingHenselLiftUnique
public import Nyll.AlgebraicCurves.Places.Completion
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.FiniteIntegerModule
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.Norm
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.HigherUnitBaseChange
public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CyclicValueGroup
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete

/-!
# Norms respect ramification-weighted ray congruences

The actual finite free norm preserves congruence to one modulo an extended
base ideal. On completed DVRs, the actual valuation formula identifies the
extended `n`-th power with depth `e * n`. This includes inseparable finite
extensions of global function fields.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve
open LocalFieldTheory.DiscreteValuationField.WithZeroValuation
open ValuationTheory.DiscreteValuationField.Valuation
open AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
open scoped AlgebraicCurve.Place WithZero nonZeroDivisors

namespace FunctionField.RayClass

variable {k K L : Type*} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [FiniteDimensional K L]

/-- The finite free completed norm takes ramification-weighted depth `e * n`
into depth `n`, including integral units at zero. -/
theorem localNorm_mem_higherUnit_of_finite_integers
    (w : Place k L)
    [Module.Finite (w.restrict K).adicCompletionIntegers w.adicCompletionIntegers]
    (n : ℕ) (x : w.adicCompletionˣ)
    (hx : x ∈ localHigherUnitGroup w (w.ramificationIndex K * n)) :
    IdeleGroup.localNorm (K := K) w x ∈ localHigherUnitGroup (w.restrict K) n := by
  by_cases hn : n = 0
  · rw [hn, localHigherUnitGroup_zero]
    exact IdeleGroup.localNorm_mem_localUnits w x
      (localHigherUnitGroup_le_localUnits w _ hx)
  have hnpos : 1 ≤ n := Nat.pos_of_ne_zero hn
  let F := (w.restrict K).adicCompletion
  let E := w.adicCompletion
  let A := (w.restrict K).adicCompletionIntegers
  let B := w.adicCompletionIntegers
  let νF : Valuation F ℤᵐ⁰ := Valued.v
  let νE : Valuation E ℤᵐ⁰ := Valued.v
  have hinj : Function.Injective (algebraMap A B) := by
    intro a b hab
    apply Subtype.ext
    exact (Place.kw_ffgc_adicCompletionComap K w).injective (congrArg Subtype.val hab)
  let : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  let : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) E :=
    AlgebraNormAlgebraMapIsPushoutIs.Algebra.NormBaseChange.isLocalization_of_finite A B E hinj
  have hxunit : x ∈ B.units := localHigherUnitGroup_le_localUnits w _ hx
  let b : B := ⟨(x : E), (Submonoid.mem_units_iff _ x).mp hxunit |>.1⟩
  obtain ⟨π₀, hπ₀⟩ :=
    exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective
      νF ((w.restrict K).heightOneSpectrum.valuedAdicCompletion_surjective K)
  let π : A := π₀
  have hπ : νF (π : F) = WithZero.exp (-1) := hπ₀
  have hπu := isUniformizer_of_valuation_eq_exp_neg_one νF (π : F) hπ
  have hπn : νF ((π : F) ^ n) = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg_one]
  have hgen : IsLocalRing.maximalIdeal A = Ideal.span ({π} : Set A) :=
    hπu.is_generator
  have hxmap : b - 1 ∈
      (IsLocalRing.maximalIdeal A ^ n).map (algebraMap A B) := by
    have hp : (IsLocalRing.maximalIdeal A) ^ n = Ideal.span ({π ^ n} : Set A) :=
      (congrArg (fun I : Ideal A => I ^ n) hgen).trans (Ideal.span_singleton_pow π n)
    rw [hp, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    apply (Valuation.Integers.dvd_iff_le (Valuation.valuationSubring.integers (v := νE))).mpr
    have hbound := (localHigherUnitGroup_iff_valuation_sub_one_le w x
      (Nat.mul_pos (w.ramificationIndex_pos (F := K)) hnpos)).mp hx
    change νE ((x : E) - 1) ≤ νE (algebraMap F E ((π : F) ^ n))
    rw [Place.algebraMap_adicCompletionComap_eq, Place.valued_adicCompletionComap,
      hπn, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg, ← Nat.cast_mul]
    exact hbound
  have hnorm := Algebra.norm_sub_one_mem_of_sub_one_mem_map
    (IsLocalRing.maximalIdeal A ^ n) b hxmap
  have hval :=
    (mem_maximalIdeal_pow_iff_valuation_le_uniformizer_pow νF hπu n).mp hnorm
  change νF (algebraMap A F (Algebra.norm A b) - 1) ≤ νF ((π : F) ^ n) at hval
  rw [hπn] at hval
  apply (localHigherUnitGroup_iff_valuation_sub_one_le (w.restrict K) _ hnpos).mpr
  change νF (Algebra.norm F (algebraMap B E b) - 1) ≤ _
  rw [Algebra.norm_localization A A⁰ (Rₘ := F) (Sₘ := E) b]
  exact hval

/-- Every finite extension of global function fields has the required finite
integer module, so the actual norm preserves divisor-pullback ray depths
without a separability assumption. -/
theorem localNorm_mem_higherUnit
    [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    (w : Place k L) (n : ℕ) (x : w.adicCompletionˣ)
    (hx : x ∈ localHigherUnitGroup w (w.ramificationIndex K * n)) :
    IdeleGroup.localNorm (K := K) w x ∈ localHigherUnitGroup (w.restrict K) n := by
  let : Module.Finite (w.restrict K).adicCompletionIntegers w.adicCompletionIntegers :=
    FunctionField.moduleFinite_adicCompletionIntegers w
  exact localNorm_mem_higherUnit_of_finite_integers w n x hx

end FunctionField.RayClass

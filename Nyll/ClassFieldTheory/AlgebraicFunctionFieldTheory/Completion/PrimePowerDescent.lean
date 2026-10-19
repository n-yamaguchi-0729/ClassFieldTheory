/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
import Nyll.AlgebraicCurves.Places.Completion
import Nyll.AlgebraicCurves.Places.Taylor.UniquePDigitsTranscendental
import Nyll.AlgebraicCurves.Places.Orders.TranscendentalOrdNeZero
import Nyll.AlgebraicCurves.FunctionFields.Extensions.FiniteSimpleExtensions
import Nyll.SchemeTheory.FunctionFields.FrobeniusSubfield

/-!
# Detecting prime powers in one completion

A uniformizer is a p-basis element globally and remains a non-pth-power
in the completion because its order is one. Comparing its p-digit
coefficients shows that an element which becomes a pth power was already
a pth power in the function field.
-/

noncomputable section
open AlgebraicCurve
open scoped WithZero

namespace FunctionField

variable {k K : Type*} [Field k] [PerfectField k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- A pth root in an actual place completion descends to the global field. -/
theorem exists_pow_eq_of_completion_pow_eq (v : Place k K)
    (p : ℕ) [Fact p.Prime] [CharP K p] (a : K)
    (x : v.adicCompletion) (hx : x ^ p = algebraMap K v.adicCompletion a) :
    ∃ b : K, b ^ p = a := by
  classical
  have hkp : CharP k p := (Algebra.charP_iff k K p).mpr inferInstance
  have hvp : CharP v.adicCompletion p :=
    (Algebra.charP_iff K v.adicCompletion p).mp inferInstance
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  let t : K := π
  have htord : v.ord t = 1 := v.ord_coe_irreducible hπ
  have htne : t ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  let tv : v.adicCompletion := algebraMap K v.adicCompletion t
  have htv : Valued.v tv = WithZero.exp (-1 : ℤ) := by
    rw [valued_algebraMap_adicCompletion]
    change v.adicValuation t = WithZero.exp (-1 : ℤ)
    have hvalue : v.adicValuation t = WithZero.exp (-v.ord t) := by
      rw [Place.ord, neg_neg, WithZero.exp_log (v.adicValuation_ne_zero htne)]
    rw [hvalue, htord]
  have htvnot : ∀ y : v.adicCompletion, y ^ p ≠ tv := by
    intro y hy
    have hval := congrArg (fun z : v.adicCompletion => WithZero.log (Valued.v z)) hy
    rw [map_pow, WithZero.log_pow, htv, WithZero.log_exp, nsmul_eq_mul] at hval
    have hprod : (p : ℤ) * (-WithZero.log (Valued.v y)) = 1 := by nlinarith
    have hp1 := Int.eq_one_of_mul_eq_one_right
      (show (0 : ℤ) ≤ p from Int.natCast_nonneg p) hprod
    have hp : 1 < p := (Fact.out : p.Prime).one_lt
    omega
  have htnot : ∀ b : K, b ^ p ≠ t := by
    intro b hb
    apply htvnot (algebraMap K v.adicCompletion b)
    rw [← map_pow, hb]
  have httr : Transcendental k t :=
    v.transcendental_of_ord_ne_zero (htord ▸ one_ne_zero)
  have hbase : FiniteDimensional
      (IntermediateField.adjoin k {algebraMap (RatFunc k) K (RatFunc.X : RatFunc k)}) K :=
    FunctionField.FiniteDimensional.adjoin_algebraMap_X (F := k) (K := K)
  have htfinite : FiniteDimensional (IntermediateField.adjoin k {t}) K :=
    finiteDimensional_adjoin_of_transcendental
      (algebraMap (RatFunc k) K (RatFunc.X : RatFunc k)) httr
  obtain ⟨c, hc, hcu⟩ := existsUnique_pDigits_of_transcendental p t httr htnot a
  let Fp : Subfield v.adicCompletion := (frobenius v.adicCompletion p).fieldRange
  let d : Fin p → Fp := fun i =>
    ⟨(algebraMap K v.adicCompletion (c i)) ^ p, ⟨algebraMap K v.adicCompletion (c i), rfl⟩⟩
  let e : Fin p → Fp := fun i =>
    if i = ⟨0, (Fact.out : p.Prime).pos⟩ then ⟨x ^ p, ⟨x, rfl⟩⟩ else 0
  have hsum : ∑ i : Fin p, d i • tv ^ (i : ℕ) =
      ∑ i : Fin p, e i • tv ^ (i : ℕ) := by
    have hleft : ∑ i : Fin p, d i • tv ^ (i : ℕ) =
        algebraMap K v.adicCompletion a := by
      rw [hc, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      change (algebraMap K v.adicCompletion (c i)) ^ p *
        (algebraMap K v.adicCompletion t) ^ (i : ℕ) = _
      rw [map_mul, map_pow, map_pow]
    rw [hleft, ← hx]
    simp only [e, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      pow_zero, Subfield.smul_def, smul_eq_mul, mul_one]
  have hcoeff := (Fintype.linearIndependent_iffₛ.mp
    (linearIndependent_pow_over_frobenius p htvnot)) d e hsum
  have hzero := congrArg Subtype.val (hcoeff ⟨0, (Fact.out : p.Prime).pos⟩)
  have hx0 : (algebraMap K v.adicCompletion (c ⟨0, (Fact.out : p.Prime).pos⟩)) ^ p =
      x ^ p := by
    simpa only [d, e, ite_true] using hzero
  refine ⟨c ⟨0, (Fact.out : p.Prime).pos⟩, (algebraMap K v.adicCompletion).injective ?_⟩
  rw [map_pow, hx0, hx]

end FunctionField

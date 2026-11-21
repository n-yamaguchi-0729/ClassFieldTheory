/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.LocalField
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChange
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.FixedIdeles
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Basic
public import Nyll.AlgebraicCurves.Places.Completion
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitValuation

/-!
# Higher ray units under the actual completion inclusion

The completion valuation scales by the ramification index. Accordingly,
pullback of depth `e * n` is exactly depth `n`, including the separate
integral-unit level at zero. Coefficient reindexing preserves every depth.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place ValuativeRel WithZero

namespace FunctionField.RayClass

variable {k K L : Type*} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [FiniteDimensional K L]

/-- Positive local ray depths are measured by the original normalized completion valuation. -/
theorem localHigherUnitGroup_iff_valuation_sub_one_le
    (v : Place k K) (x : v.adicCompletionˣ) {n : ℕ} (hn : 1 ≤ n) :
    x ∈ localHigherUnitGroup v n ↔
      Valued.v ((x : v.adicCompletion) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  let : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
  let ν : Valuation v.adicCompletion ℤᵐ⁰ := Valued.v
  let : ν.Compatible := Valuation.Compatible.ofValuation ν
  exact LocalFieldTheory.mem_fieldPrincipalUnits_iff_valuation_sub_one_le
    v.adicCompletion ν (v.heightOneSpectrum.valuedAdicCompletion_surjective K) x hn

/-- The actual completion embedding multiplies the order of `x - 1` by its
ramification index, expressed without excluding `x = 1`. -/
theorem localBaseChange_sub_one_valuation (w : Place k L)
    (x : (w.restrict K).adicCompletionˣ) :
    Valued.v (((IdeleGroup.localBaseChange (K := K) w x : w.adicCompletionˣ) :
      w.adicCompletion) - 1) =
      (Valued.v ((x : (w.restrict K).adicCompletion) - 1) : ℤᵐ⁰) ^
        w.ramificationIndex K := by
  change Valued.v (algebraMap (w.restrict K).adicCompletion w.adicCompletion (x : _) - 1) = _
  rw [← map_one (algebraMap (w.restrict K).adicCompletion w.adicCompletion),
    ← map_sub, Place.algebraMap_adicCompletionComap_eq, Place.valued_adicCompletionComap]

/-- The preimage of a ramification-weighted principal-unit level is exactly
the original level. Depth zero is the ordinary integral-unit condition. -/
theorem localBaseChange_mem_mulHigherUnit_iff
    (w : Place k L) (n : ℕ) (x : (w.restrict K).adicCompletionˣ) :
    IdeleGroup.localBaseChange (K := K) w x ∈
        localHigherUnitGroup w (w.ramificationIndex K * n) ↔
      x ∈ localHigherUnitGroup (w.restrict K) n := by
  by_cases hn : n = 0
  · rw [hn, mul_zero, localHigherUnitGroup_zero, localHigherUnitGroup_zero]
    exact IdeleGroup.localBaseChange_mem_localUnits_iff w x
  · have hpos : 1 ≤ n := Nat.pos_of_ne_zero hn
    have hmulpos : 1 ≤ w.ramificationIndex K * n :=
      Nat.mul_pos (w.ramificationIndex_pos (F := K)) hpos
    rw [localHigherUnitGroup_iff_valuation_sub_one_le w _ hmulpos,
      localHigherUnitGroup_iff_valuation_sub_one_le (w.restrict K) x hpos,
      localBaseChange_sub_one_valuation]
    have hpow : WithZero.exp (-((w.ramificationIndex K * n : ℕ) : ℤ)) =
        WithZero.exp (-(n : ℤ)) ^ w.ramificationIndex K := by
      rw [Nat.cast_mul, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg]
    rw [hpow]
    exact pow_le_pow_iff_left₀ zero_le zero_le (w.ramificationIndex_pos (F := K)).ne'

/-- Coefficient reindexing preserves higher units at every depth, even in a
ramified extension. -/
theorem localBaseChange_mem_higherUnit
    (w : Place k L) (n : ℕ) (x : (w.restrict K).adicCompletionˣ)
    (hx : x ∈ localHigherUnitGroup (w.restrict K) n) :
    IdeleGroup.localBaseChange (K := K) w x ∈ localHigherUnitGroup w n := by
  have hw := w.ramificationIndex_pos (F := K)
  apply localHigherUnitGroup_antitone w (Nat.le_mul_of_pos_left n hw)
  exact (localBaseChange_mem_mulHigherUnit_iff w n x).mpr hx

private theorem pow_le_exp_neg_ceil_iff (a : ℤᵐ⁰) (e r : ℕ)
    (he : 0 < e) (hr : 1 ≤ r) :
    a ^ e ≤ WithZero.exp (-(r : ℤ)) ↔
      a ≤ WithZero.exp (-(((r - 1) / e + 1 : ℕ) : ℤ)) := by
  by_cases ha : a = 0
  · rw [ha, zero_pow he.ne']
    exact iff_of_true bot_le bot_le
  · have hlo := Nat.div_mul_le_self (r - 1) e
    have hhi := Nat.lt_mul_div_succ (r - 1) he
    have hlo' : (((r - 1) / e : ℕ) : ℤ) * e < r := by
      exact_mod_cast (show (r - 1) / e * e < r by omega)
    have hhi' : (r : ℤ) ≤ (e : ℤ) * ((((r - 1) / e : ℕ) : ℤ) + 1) := by
      exact_mod_cast (show r ≤ e * ((r - 1) / e + 1) by omega)
    have he' : (0 : ℤ) < e := by exact_mod_cast he
    have hrepr : a = WithZero.exp (WithZero.log a) := (WithZero.exp_log ha).symm
    conv_lhs => rw [hrepr]
    conv_rhs => rw [hrepr]
    rw [← WithZero.exp_nsmul, nsmul_eq_mul, WithZero.exp_le_exp, WithZero.exp_le_exp,
      Nat.cast_add, Nat.cast_one]
    constructor
    · intro h
      by_contra hnot
      have hz : -(((r - 1) / e : ℕ) : ℤ) ≤ WithZero.log a := by omega
      have hmul := mul_le_mul_of_nonneg_left hz he'.le
      nlinarith
    · intro h
      have hmul := mul_le_mul_of_nonneg_left h he'.le
      nlinarith

/-- At arbitrary positive target depth, the preimage exponent is the ceiling
of `r / e`, written without truncated subtraction at zero. -/
theorem localBaseChange_mem_higherUnit_iff_ceil
    (w : Place k L) (r : ℕ) (hr : 1 ≤ r) (x : (w.restrict K).adicCompletionˣ) :
    IdeleGroup.localBaseChange (K := K) w x ∈ localHigherUnitGroup w r ↔
      x ∈ localHigherUnitGroup (w.restrict K) ((r - 1) / w.ramificationIndex K + 1) := by
  rw [localHigherUnitGroup_iff_valuation_sub_one_le w _ hr,
    localHigherUnitGroup_iff_valuation_sub_one_le (w.restrict K) x (Nat.succ_pos _),
    localBaseChange_sub_one_valuation]
  exact pow_le_exp_neg_ceil_iff _ _ _ w.ramificationIndex_pos hr

/-- With ramification index one, coefficient reindexing also reflects all depths. -/
theorem localBaseChange_mem_higherUnit_iff_of_unramified
    (w : Place k L) (he : w.ramificationIndex K = 1)
    (n : ℕ) (x : (w.restrict K).adicCompletionˣ) :
    IdeleGroup.localBaseChange (K := K) w x ∈ localHigherUnitGroup w n ↔
      x ∈ localHigherUnitGroup (w.restrict K) n := by
  simpa only [he, one_mul] using localBaseChange_mem_mulHigherUnit_iff w n x

end FunctionField.RayClass

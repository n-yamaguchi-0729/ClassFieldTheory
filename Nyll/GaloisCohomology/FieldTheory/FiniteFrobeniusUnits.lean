/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.FieldTheory.FiniteFrobeniusTower
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Frobenius periods and multiplicative Lang primitives in algebraic constants

A single algebraic constant lies in an actual finite subextension.
Over an algebraic closure, the multiplicative Lang equation for every positive
Frobenius power reduces to taking a nonzero root of a positive power.
-/

noncomputable section

namespace FiniteField

variable (k Ω : Type*) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω]

/-- The elements fixed by arithmetic Frobenius are precisely the original constants. -/
theorem frobenius_eq_self_iff_mem_range (a : Ω) :
    frobeniusAlgEquivOfAlgebraic k Ω a = a ↔ a ∈ Set.range (algebraMap k Ω) := by
  constructor
  · intro h
    have hs : (Polynomial.X ^ Fintype.card k - Polynomial.X : Polynomial k).Splits := by
      rw [Polynomial.splits_iff_card_roots, roots_X_pow_card_sub_X, ← Finset.card_def,
        Finset.card_univ, X_pow_card_sub_X_natDegree_eq k Fintype.one_lt_card]
    apply hs.mem_range_of_isRoot (X_pow_card_sub_X_ne_zero k Fintype.one_lt_card)
    change a ^ Fintype.card k = a at h
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    exact sub_eq_zero.mpr h
  · rintro ⟨b, rfl⟩
    exact (frobeniusAlgEquivOfAlgebraic k Ω).commutes b

/-- Every algebraic constant has a positive arithmetic Frobenius period. -/
theorem exists_frobenius_period (x : Ω) :
    ∃ n : ℕ, n ≠ 0 ∧ (frobeniusAlgEquivOfAlgebraic k Ω ^ n) x = x := by
  let E := IntermediateField.adjoin k ({x} : Set Ω)
  have : Module.Finite k E := IntermediateField.finiteDimensional_adjoin
    (fun y _ => Algebra.IsIntegral.isIntegral (R := k) y)
  have : Finite E := Module.finite_of_finite k
  let : Fintype E := Fintype.ofFinite E
  have : Algebra.IsAlgebraic E Ω := Algebra.IsAlgebraic.tower_top (K := k) E
  let a : E := ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩
  refine ⟨Module.finrank k E, (Module.finrank_pos (R := k) (M := E)).ne', ?_⟩
  change (frobeniusAlgEquivOfAlgebraic k Ω ^ Module.finrank k E) (algebraMap E Ω a) =
    algebraMap E Ω a
  rw [← frobeniusAlgEquiv_restrictScalars k E Ω]
  exact (frobeniusAlgEquivOfAlgebraic E Ω).commutes a

/-- Multiplicative Lang for every positive Frobenius power on actual algebraic constants. -/
theorem exists_unit_frobenius_pow_div [IsAlgClosed Ω] (n : ℕ) (hn : n ≠ 0) (c : Ωˣ) :
    ∃ a : Ωˣ, ((frobeniusAlgEquivOfAlgebraic k Ω ^ n) • a) / a = c := by
  have hq : 1 < Fintype.card k ^ n := one_lt_pow₀ (Fintype.one_lt_card) hn
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (c : Ω)
    (Nat.sub_pos_of_lt hq)
  have ha0 : a ≠ 0 := by
    intro hzero
    apply c.ne_zero
    rw [← ha, hzero, zero_pow (Nat.sub_pos_of_lt hq).ne']
  refine ⟨Units.mk0 a ha0, ?_⟩
  apply Units.ext
  simp only [Units.val_div_eq_div_val, AlgEquiv.smul_units_def, Units.coe_map, Units.val_mk0]
  change (frobeniusAlgEquivOfAlgebraic k Ω ^ n) a / a = (c : Ω)
  rw [AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate]
  apply (div_eq_iff ha0).mpr
  rw [← ha, ← pow_succ]
  exact congrArg (a ^ ·) (Nat.sub_add_cancel hq.le).symm

end FiniteField

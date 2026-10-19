/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# Periodic primitives from the Lang operator

If the difference between a cyclic action and the identity is surjective on an
ambient module, a zero-norm element has a primitive fixed by the corresponding
power. The proof uses the actual telescoping cyclic sum.
-/

noncomputable section

namespace CyclicAction

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- The cyclic sum of a coboundary telescopes to the difference of its endpoints. -/
theorem sum_range_smul_sub (σ : G) (n : ℕ) (x : A) :
    ∑ i ∈ Finset.range n, σ ^ i • (σ • x - x) = σ ^ n • x - x := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, pow_zero, one_smul, sub_self]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, smul_sub, ← mul_smul, ← pow_succ]
    rw [add_comm, sub_add_sub_cancel]

/-- Surjectivity of the Lang operator gives a periodic primitive of every zero-norm element. -/
theorem exists_fixed_primitive_of_surjective_sub (σ : G)
    (hσ : Function.Surjective (fun x : A => σ • x - x)) (n : ℕ) (y : A)
    (hy : ∑ i ∈ Finset.range n, σ ^ i • y = 0) :
    ∃ x : A, σ ^ n • x = x ∧ σ • x - x = y := by
  obtain ⟨x, hx⟩ := hσ y
  change σ • x - x = y at hx
  refine ⟨x, ?_, hx⟩
  apply sub_eq_zero.mp
  rw [← sum_range_smul_sub, hx, hy]

/-- Lang surjectivity for a power makes the corresponding norm onto the fixed elements. -/
theorem exists_fixed_norm_preimage_of_surjective_sub_pow (σ : G) (n : ℕ)
    (hσn : Function.Surjective (fun x : A => σ ^ n • x - x)) (y : A)
    (hy : σ • y = y) :
    ∃ x : A, σ ^ n • x = x ∧ ∑ i ∈ Finset.range n, σ ^ i • x = y := by
  obtain ⟨z, hz⟩ := hσn y
  change σ ^ n • z - z = y at hz
  have hz' : σ ^ n • z = y + z := (sub_eq_iff_eq_add).mp hz
  refine ⟨σ • z - z, ?_, (sum_range_smul_sub σ n z).trans hz⟩
  rw [smul_sub, ← mul_smul, ← pow_succ, pow_succ', mul_smul, hz', smul_add, hy]
  exact add_sub_add_left_eq_sub (σ • z) z y

/-- The difference of the cyclic sum is the same telescoping norm of a difference. -/
theorem smul_sum_range_sub (σ : G) (n : ℕ) (x : A) :
    σ • (∑ i ∈ Finset.range n, σ ^ i • x) - (∑ i ∈ Finset.range n, σ ^ i • x) =
      σ ^ n • x - x := by
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib, ← sum_range_smul_sub]
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_sub, ← mul_smul, ← mul_smul, ← pow_succ', ← pow_succ]

/-- Surjectivity of a positive power's Lang operator implies surjectivity of the original one. -/
theorem surjective_sub_of_surjective_sub_pow (σ : G) (n : ℕ)
    (hσn : Function.Surjective (fun x : A => σ ^ n • x - x)) :
    Function.Surjective (fun x : A => σ • x - x) := by
  intro y
  obtain ⟨x, hx⟩ := hσn y
  exact ⟨∑ i ∈ Finset.range n, σ ^ i • x, (smul_sum_range_sub σ n x).trans hx⟩

end CyclicAction

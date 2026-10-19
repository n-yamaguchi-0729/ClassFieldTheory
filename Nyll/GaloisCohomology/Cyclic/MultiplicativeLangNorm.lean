/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Multiplicative cyclic norms and Lang primitives

Telescoping products supply periodic norm preimages from a multiplicative
Lang equation. The formulas apply to actual field units and retain the period.
-/

namespace CyclicAction

variable {G A : Type*} [Group G] [CommGroup A] [MulDistribMulAction G A]

/-- The norm of a multiplicative coboundary is its endpoint quotient. -/
theorem prod_range_smul_div (σ : G) (n : ℕ) (x : A) :
    ∏ i ∈ Finset.range n, σ ^ i • ((σ • x) / x) = (σ ^ n • x) / x := by
  simp only [smul_div', ← mul_smul, ← pow_succ]
  simpa only [pow_zero, one_smul] using
    Finset.prod_range_div (fun i : ℕ => σ ^ i • x) n

/-- The quotient of a norm and its translate is the endpoint quotient. -/
theorem smul_prod_range_div (σ : G) (n : ℕ) (x : A) :
    (σ • (∏ i ∈ Finset.range n, σ ^ i • x)) / (∏ i ∈ Finset.range n, σ ^ i • x) =
      (σ ^ n • x) / x := by
  rw [Finset.smul_prod', ← Finset.prod_div_distrib]
  simp only [← mul_smul, ← pow_succ']
  simpa only [pow_zero, one_smul] using
    Finset.prod_range_div (fun i : ℕ => σ ^ i • x) n

/-- A multiplicative Lang primitive for a fixed element gives a periodic norm preimage. -/
theorem exists_periodic_norm_preimage_of_surjective_div_pow (σ : G) (n : ℕ)
    (hLang : Function.Surjective (fun x : A => (σ ^ n • x) / x))
    (y : A) (hy : σ • y = y) :
    ∃ x : A, σ ^ n • x = x ∧ ∏ i ∈ Finset.range n, σ ^ i • x = y := by
  obtain ⟨z, hz⟩ := hLang y
  change (σ ^ n • z) / z = y at hz
  have hz' : σ ^ n • z = y * z := div_eq_iff_eq_mul.mp hz
  refine ⟨(σ • z) / z, ?_, (prod_range_smul_div σ n z).trans hz⟩
  rw [smul_div', ← mul_smul, ← pow_succ, pow_succ', mul_smul, hz', smul_mul', hy]
  exact mul_div_mul_left_eq_div (σ • z) z y

end CyclicAction

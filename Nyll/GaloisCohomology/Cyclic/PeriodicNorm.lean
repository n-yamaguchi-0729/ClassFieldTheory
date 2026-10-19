/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Cyclic.LangNormKernel
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Norms between periodic subgroups

For a single automorphism, the length-n cyclic sum maps its period-n subgroup
to its fixed subgroup. The coboundary on the period-n subgroup has norm zero.
These maps do not require the automorphism to have finite order on the ambient group.
-/

namespace CyclicAction

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- Elements fixed by the specified power of an actual action. -/
def periodicSubgroup (σ : G) (n : ℕ) : AddSubgroup A where
  carrier := {x | σ ^ n • x = x}
  zero_mem' := smul_zero _
  add_mem' {x y} hx hy := (smul_add (σ ^ n) x y).trans (congrArg₂ (· + ·) hx hy)
  neg_mem' {x} hx := (smul_neg (σ ^ n) x).trans (congrArg Neg.neg hx)

/-- Multiples of a period fix every element fixed by the original period. -/
theorem periodicSubgroup_le_mul (σ : G) (n m : ℕ) :
    periodicSubgroup (A := A) σ n ≤ periodicSubgroup (A := A) σ (n * m) := by
  intro x hx
  have hx' : σ ^ n • x = x := hx
  change σ ^ (n * m) • x = x
  induction m with
  | zero => rw [Nat.mul_zero, pow_zero, one_smul]
  | succ m ih => rw [Nat.mul_succ, pow_add, mul_smul, hx', ih]

/-- The cyclic norm from period-n elements to fixed elements. -/
def periodicNorm (σ : G) (n : ℕ) : periodicSubgroup (A := A) σ n →+
    periodicSubgroup (A := A) σ 1 where
  toFun x := ⟨∑ i ∈ Finset.range n, σ ^ i • (x : A), by
    change σ ^ 1 • (∑ i ∈ Finset.range n, σ ^ i • (x : A)) =
      ∑ i ∈ Finset.range n, σ ^ i • (x : A)
    rw [pow_one]
    apply sub_eq_zero.mp
    exact (smul_sum_range_sub σ n (x : A)).trans (by rw [x.property, sub_self])⟩
  map_zero' := Subtype.ext (by simp only [AddSubgroup.coe_zero, smul_zero, Finset.sum_const_zero])
  map_add' x y := Subtype.ext (by
    simp only [AddSubgroup.coe_add, smul_add, Finset.sum_add_distrib])

/-- The value of the periodic norm is the actual cyclic sum. -/
theorem periodicNorm_coe (σ : G) (n : ℕ) (x : periodicSubgroup (A := A) σ n) :
    (periodicNorm σ n x : A) = ∑ i ∈ Finset.range n, σ ^ i • (x : A) := rfl

/-- The coboundary preserves period-n elements. -/
def periodicCoboundary (σ : G) (n : ℕ) : periodicSubgroup (A := A) σ n →+
    periodicSubgroup (A := A) σ n where
  toFun x := ⟨σ • (x : A) - x, by
    change σ ^ n • (σ • (x : A) - x) = σ • (x : A) - x
    rw [smul_sub, ← mul_smul, ← pow_succ, pow_succ', mul_smul, x.property]⟩
  map_zero' := Subtype.ext (by simp only [AddSubgroup.coe_zero, smul_zero, sub_self])
  map_add' x y := Subtype.ext (by
    simp only [AddSubgroup.coe_add, smul_add]
    exact add_sub_add_comm _ _ _ _)

/-- Every periodic coboundary has zero periodic norm. -/
theorem periodicNorm_coboundary (σ : G) (n : ℕ)
    (x : periodicSubgroup (A := A) σ n) :
    periodicNorm σ n (periodicCoboundary σ n x) = 0 := by
  apply Subtype.ext
  change (∑ i ∈ Finset.range n, σ ^ i • (σ • (x : A) - x)) = 0
  rw [sum_range_smul_sub, x.property, sub_self]

/-- A primitive for every norm-zero element gives exactness of the periodic norm sequence. -/
theorem range_periodicCoboundary_eq_ker (σ : G) (n : ℕ)
    (h : ∀ x : A, (∑ i ∈ Finset.range n, σ ^ i • x) = 0 →
      ∃ y : A, σ ^ n • y = y ∧ σ • y - y = x) :
    (periodicCoboundary (A := A) σ n).range = (periodicNorm (A := A) σ n).ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact periodicNorm_coboundary σ n y
  · intro hx
    have hzero : (∑ i ∈ Finset.range n, σ ^ i • (x : A)) = 0 :=
      congrArg Subtype.val hx
    obtain ⟨y, hy, he⟩ := h x hzero
    exact ⟨⟨y, hy⟩, Subtype.ext he⟩

end CyclicAction

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Nyll.AlgebraicCurves.Divisors.Degree.DegreeArithmetic

/-!
# A consequence of the principal-divisor product formula

A nonzero function integral at every place cannot have positive order at a place of positive
residue degree. This argument is shared by the discreteness of principal ideles and the
identification of the full constant field.
-/

namespace FunctionField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
  [AlgebraicCurve.HasPrincipalDivisors k K]

/-- A nonzero function with no poles has zero order at every place of finite residue degree. -/
theorem ord_eq_zero_of_forall_ord_nonneg (v : AlgebraicCurve.Place k K)
    [Module.Finite k v.ResidueField] {f : K} (hf : f ≠ 0)
    (hnonneg : ∀ w : AlgebraicCurve.Place k K, 0 ≤ w.ord f) : v.ord f = 0 := by
  classical
  refine le_antisymm ?_ (hnonneg v)
  by_contra hnot
  have hpos : 0 < v.ord f := lt_of_not_ge hnot
  obtain ⟨D, hD, hdegree⟩ :=
    AlgebraicCurve.HasPrincipalDivisors.exists_divisor (K := k) (F := K) f hf
  have hvD : v ∈ D.support := Finsupp.mem_support_iff.mpr (by
    rw [hD v]
    exact ne_of_gt hpos)
  have hdeg : 0 < (v.deg : ℤ) := by
    exact_mod_cast (Module.finrank_pos (R := k) (M := v.ResidueField))
  have hpositive : 0 < AlgebraicCurve.Divisor.degree D := by
    rw [AlgebraicCurve.Divisor.degree_eq_sum_support]
    apply Finset.sum_pos'
    · intro w _
      rw [hD w]
      exact mul_nonneg (hnonneg w) (Int.natCast_nonneg w.deg)
    · refine ⟨v, hvD, ?_⟩
      rw [hD v]
      exact mul_pos hpos hdeg
  rw [hdegree] at hpositive
  exact lt_irrefl 0 hpositive

end FunctionField

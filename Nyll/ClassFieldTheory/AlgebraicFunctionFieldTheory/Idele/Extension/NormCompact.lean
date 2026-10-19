/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.Int.Interval
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Degree
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.DegreeFibers
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTopology
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormClosed

/-!
# Compactness of the actual norm quotient

A positive-degree idele class exists without a degree-one place. Its power by
the extension degree belongs to the actual norm image. Dividing any class by
a suitable integer power of this norm reduces its degree to a fixed finite
interval. The compact degree fibers over that interval cover the norm quotient.
Compactness does not by itself assert finiteness or the class-field norm index.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup

variable {k K L : Type*} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- The quotient of idele classes by the actual finite-extension norm image is compact. -/
theorem normQuotient_compactSpace :
    CompactSpace (IdeleClassGroup k K ⧸ (norm (k := k) (K := K) (L := L)).range) := by
  classical
  let N := (norm (k := k) (K := K) (L := L)).range
  have : N.Normal := ⟨fun a ha g => by
    simpa only [mul_comm g a, mul_assoc, mul_inv_cancel, mul_one] using ha⟩
  let q : IdeleClassGroup k K →* IdeleClassGroup k K ⧸ N := QuotientGroup.mk' N
  obtain ⟨c, hc⟩ := exists_positive_degree (k := k) (K := K)
  let a : IdeleClassGroup k K := c ^ Module.finrank K L
  let d : ℤ := (degree (k := k) (K := K) a).toAdd
  have hd : 0 < d := by
    change 0 < (degree (k := k) (K := K) (c ^ Module.finrank K L)).toAdd
    rw [map_pow, toAdd_pow, nsmul_eq_mul]
    exact mul_pos (Int.natCast_pos.mpr Module.finrank_pos) hc
  have ha : a ∈ N := ⟨baseChange (k := k) (K := K) (L := L) c, norm_baseChange c⟩
  have hqa : q a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
  let S : Set (IdeleClassGroup k K) :=
    ⋃ i ∈ Finset.Ico (0 : ℤ) d,
      (degree (k := k) (K := K)) ⁻¹' {Multiplicative.ofAdd i}
  have hS : IsCompact S :=
    (Finset.Ico (0 : ℤ) d).isCompact_biUnion (fun i _ => isCompact_degree_fiber _)
  have hcover : q '' S = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N z
    let n : ℤ := (degree (k := k) (K := K) b).toAdd
    let b' : IdeleClassGroup k K := b / a ^ (n / d)
    have hb' : (degree (k := k) (K := K) b').toAdd = n % d := by
      change (degree (k := k) (K := K) (b / a ^ (n / d))).toAdd = n % d
      rw [map_div, map_zpow, toAdd_div, toAdd_zpow, zsmul_eq_mul]
      change n - (n / d) * d = n % d
      rw [mul_comm (n / d) d]
      exact (Int.emod_def n d).symm
    refine ⟨b', ?_, ?_⟩
    · apply Set.mem_iUnion.mpr
      refine ⟨n % d, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_Ico.mpr ⟨Int.emod_nonneg n hd.ne', Int.emod_lt_of_pos n hd⟩
      · exact Multiplicative.ext hb'
    · change q (b / a ^ (n / d)) = q b
      rw [map_div, map_zpow, hqa, one_zpow, div_one]
  apply isCompact_univ_iff.mp
  rw [← hcover]
  exact hS.image QuotientGroup.continuous_mk

end FunctionField.IdeleClassGroup

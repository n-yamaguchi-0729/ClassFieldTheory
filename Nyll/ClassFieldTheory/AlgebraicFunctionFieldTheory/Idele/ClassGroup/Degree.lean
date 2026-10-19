/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Constants
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Basic
import Mathlib.Basic.Finite.Defs

/-!
# The noncompact degree direction

An actual place gives an idele class of positive degree, without assuming a place
of degree one. Its integer powers show that the full idele class group is infinite.
Degrees computed over a smaller constant field retain the full constant-field factor.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]

/-- Every idele-class degree contains the full constant-field normalization factor. -/
theorem fullConstants_degree_dvd (c : IdeleClassGroup k K) :
    (Module.finrank k (algebraicClosure k K) : ℤ) ∣
      (degree (k := k) (K := K) c).toAdd := by
  obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := K) c
  exact FunctionField.fullConstants_degree_dvd_divisor_degree
    (IdeleGroup.divisor (k := k) (K := K) a).toAdd

variable [Finite k] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- The class group has a class of positive degree; no rational place is assumed. -/
theorem exists_positive_degree :
    ∃ c : IdeleClassGroup k K, 0 < (degree (k := k) (K := K) c).toAdd := by
  have : AlgebraicCurve.IsCurveOver k K := FunctionField.isCurveOver k K
  obtain ⟨v⟩ := FunctionField.nonempty_place k K
  have : Module.Finite k v.ResidueField := AlgebraicCurve.IsCurveOver.finite_residueField v
  have hv : 0 < v.deg := Module.finrank_pos
  obtain ⟨a, ha⟩ := IdeleGroup.divisor_surjective (k := k) (K := K)
    (Multiplicative.ofAdd (Finsupp.single v 1))
  refine ⟨mk (k := k) (K := K) a, ?_⟩
  rw [degree_mk, IdeleGroup.degree_apply, ha, toAdd_ofAdd,
    AlgebraicCurve.Divisor.degree_single, one_mul]
  exact Int.natCast_pos.mpr hv

/-- The full idele class group is infinite because its degree direction is nonzero. -/
theorem infinite : Infinite (IdeleClassGroup k K) := by
  obtain ⟨c, hc⟩ := exists_positive_degree (k := k) (K := K)
  have hinj : Function.Injective (fun n : ℤ => c ^ n) := by
    intro n m h
    have hd := congrArg (fun z : IdeleClassGroup k K =>
      (degree (k := k) (K := K) z).toAdd) h
    simp only [map_zpow, toAdd_zpow, zsmul_eq_mul] at hd
    exact mul_right_cancel₀ (ne_of_gt hc) hd
  exact Infinite.of_injective (fun n : ℤ => c ^ n) hinj

end FunctionField.IdeleClassGroup

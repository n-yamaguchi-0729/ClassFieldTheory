/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.DegreeOne
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.NormalizedDegree

/-!
# Surjectivity of the actual normalized idele-class degree

A degree-one divisor over the actual full constants lifts to an idele. Transport
along the constant-field equivalence gives a class of normalized degree one;
its integer powers realize all integer degrees.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup

variable {k K : Type} [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [AlgebraicCurve.HasPrincipalDivisors k K]

/-- An actual idele class has normalized degree one. -/
theorem exists_normalizedDegree_one :
    ∃ c : IdeleClassGroup k K,
      normalizedDegree (k := k) (K := K) c = Multiplicative.ofAdd 1 := by
  have hcurve : AlgebraicCurve.IsCurveOver (algebraicClosure k K) K :=
    FunctionField.isCurveOver_fullConstants k K
  have hprincipal : AlgebraicCurve.HasPrincipalDivisors (algebraicClosure k K) K :=
    AlgebraicCurve.IsCurveOver.hasPrincipalDivisors
  obtain ⟨D, hD⟩ := FunctionField.exists_fullConstants_divisor_degree_one k K
  obtain ⟨a, ha⟩ := IdeleGroup.divisor_surjective (k := algebraicClosure k K) (K := K)
    (Multiplicative.ofAdd D)
  let c := mk (k := algebraicClosure k K) (K := K) a
  refine ⟨(constantEquiv k (algebraicClosure k K) K).symm c, ?_⟩
  rw [normalizedDegree_eq_degree_constantEquiv, ContinuousMulEquiv.apply_symm_apply]
  change degree (k := algebraicClosure k K) (K := K)
    (mk (k := algebraicClosure k K) (K := K) a) = Multiplicative.ofAdd 1
  rw [degree_mk]
  apply Multiplicative.ext
  rw [IdeleGroup.degree_apply, ha, toAdd_ofAdd, hD]
  rfl

/-- The actual normalized idele-class degree is onto the integers. -/
theorem normalizedDegree_surjective :
    Function.Surjective (normalizedDegree (k := k) (K := K)) := by
  obtain ⟨c, hc⟩ := exists_normalizedDegree_one (k := k) (K := K)
  intro n
  refine ⟨c ^ n.toAdd, ?_⟩
  rw [map_zpow, hc]
  apply Multiplicative.ext
  simp only [toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul, mul_one, Int.cast_id]

end FunctionField.IdeleClassGroup

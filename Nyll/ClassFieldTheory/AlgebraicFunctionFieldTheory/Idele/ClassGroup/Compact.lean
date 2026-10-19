/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.Compact
import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.ConstantExtension
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.IntegralUnits
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Topology

/-!
# Compactness of the degree-zero idele class group

Every fibre of the divisor-class map is a translate of its compact integral-unit
kernel. The finite degree-zero Picard group supplies finitely many such fibres
covering the degree-zero idele classes. Since degree zero is a closed condition,
these classes form a compact subgroup.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup

variable {k K : Type*} [Field k] [Finite k] [Field K]
  [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] [AlgebraicCurve.HasPrincipalDivisors k K]

/-- Each divisor-class fibre is compact because it is a translate of the actual
compact subgroup of everywhere-integral idele classes. -/
theorem isCompact_divisorClass_fiber (c : Multiplicative (AlgebraicCurve.Pic k K)) :
    IsCompact {a : IdeleClassGroup k K | divisorClass (k := k) (K := K) a = c} := by
  obtain ⟨a, ha⟩ := divisorClass_surjective (k := k) (K := K) c
  have hfiber : {x : IdeleClassGroup k K | divisorClass (k := k) (K := K) x = c} =
      (fun u : IdeleClassGroup k K => a * u) ''
        (integralSubgroup (k := k) (K := K) : Set (IdeleClassGroup k K)) := by
    ext x
    constructor
    · intro hx
      refine ⟨a⁻¹ * x, ?_, mul_inv_cancel_left a x⟩
      rw [← divisorClass_ker]
      change divisorClass (k := k) (K := K) (a⁻¹ * x) = 1
      rw [map_mul, map_inv, ha, hx, inv_mul_cancel]
    · rintro ⟨u, hu, rfl⟩
      have huOne : divisorClass (k := k) (K := K) u = 1 := by
        change u ∈ (divisorClass (k := k) (K := K)).ker
        rw [divisorClass_ker]
        exact hu
      change divisorClass (k := k) (K := K) (a * u) = c
      rw [map_mul, ha, huOne, mul_one]
  rw [hfiber]
  exact (isCompact_integralSubgroup (k := k) (K := K)).image
    (continuous_const_mul a)

/-- Over any finite constant field, the degree-zero idele classes are compact. -/
theorem isCompact_degreeZero :
    IsCompact (degreeZero (k := k) (K := K) : Set (IdeleClassGroup k K)) := by
  have : Finite (AlgebraicCurve.Pic0 k K) := finite_pic0 k K
  let j : AlgebraicCurve.Pic0 k K →+ AlgebraicCurve.Pic k K :=
    QuotientAddGroup.map
      ((AlgebraicCurve.Divisor.principal (K := k) (F := K)).addSubgroupOf
        (AlgebraicCurve.Divisor.degZero (K := k) (F := K)))
      (AlgebraicCurve.Divisor.principal (K := k) (F := K))
      (AlgebraicCurve.Divisor.degZero (K := k) (F := K)).subtype (by
        intro D hD
        exact hD)
  let S : Set (IdeleClassGroup k K) :=
    ⋃ c : AlgebraicCurve.Pic0 k K,
      {a | divisorClass (k := k) (K := K) a = Multiplicative.ofAdd (j c)}
  have hS : IsCompact S :=
    isCompact_iUnion fun c : AlgebraicCurve.Pic0 k K =>
      isCompact_divisorClass_fiber (Multiplicative.ofAdd (j c))
  apply hS.of_isClosed_subset isClosed_degreeZero
  intro c hc
  obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := K) c
  have hdegree : AlgebraicCurve.Divisor.degree
      (IdeleGroup.divisor (k := k) (K := K) a).toAdd = 0 := by
    have h := (mem_degreeZero (mk (k := k) (K := K) a)).1 hc
    rw [degree_mk] at h
    exact congrArg Multiplicative.toAdd h
  apply Set.mem_iUnion.mpr
  refine ⟨AlgebraicCurve.Pic0.mk
    ⟨(IdeleGroup.divisor (k := k) (K := K) a).toAdd, hdegree⟩, ?_⟩
  change divisorClass (k := k) (K := K) (mk (k := k) (K := K) a) = _
  rw [divisorClass_mk]
  rfl

/-- Compactness uses the subgroup topology inherited from the idele class group. -/
theorem degreeZero_compactSpace :
    CompactSpace (degreeZero (k := k) (K := K)) :=
  isCompact_iff_compactSpace.mp isCompact_degreeZero

end FunctionField.IdeleClassGroup

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Maps.Proper.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Compact
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Topology

/-!
# Properness of idele-class degree

Every nonempty degree fiber is a translate of the compact degree-zero subgroup.
Since integer degree has the discrete topology, its continuous map is proper.
This does not assert that every integer is a degree of an idele class.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup

variable {k K : Type*} [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [AlgebraicCurve.HasPrincipalDivisors k K]

/-- Every fiber of the actual degree map is compact, including empty fibers. -/
theorem isCompact_degree_fiber (d : Multiplicative ℤ) :
    IsCompact ((degree (k := k) (K := K)) ⁻¹' {d}) := by
  by_cases h : ∃ c : IdeleClassGroup k K, degree (k := k) (K := K) c = d
  · obtain ⟨c, hc⟩ := h
    have hfiber : (degree (k := k) (K := K)) ⁻¹' {d} =
        (fun x : IdeleClassGroup k K => c * x) ''
          (degreeZero (k := k) (K := K) : Set (IdeleClassGroup k K)) := by
      ext x
      constructor
      · intro hx
        refine ⟨c⁻¹ * x, ?_, mul_inv_cancel_left c x⟩
        change degree (k := k) (K := K) (c⁻¹ * x) = 1
        rw [map_mul, map_inv, hc, Set.mem_preimage.mp hx, inv_mul_cancel]
      · rintro ⟨y, hy, rfl⟩
        change degree (k := k) (K := K) (c * y) = d
        rw [map_mul, hc, (mem_degreeZero y).mp hy, mul_one]
    rw [hfiber]
    exact isCompact_degreeZero.image (continuous_const_mul c)
  · have hempty : (degree (k := k) (K := K)) ⁻¹' {d} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro c hc
      exact h ⟨c, hc⟩
    rw [hempty]
    exact isCompact_empty

/-- The class-degree map is proper, with its actual compact fibers. -/
theorem isProperMap_degree : IsProperMap (degree (k := k) (K := K)) := by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  exact ⟨continuous_degree, fun _ _ => isClosed_discrete _, isCompact_degree_fiber⟩

end FunctionField.IdeleClassGroup

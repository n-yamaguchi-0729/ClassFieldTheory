/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_pushforwardNormFormula_of_isSeparable.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Divisors.Maps.Maps
public import Nyll.AlgebraicCurves.Places.NormTrace.OrdNormEqSumFiberOverSeparable

/-! # The divisor pushforward formula for a finite separable extension -/

@[expose] public section

open scoped BigOperators

namespace AlgebraicCurve.Divisor

/-- Divisor pushforward sends a principal divisor to the divisor of the field norm. -/
theorem pushforwardNormFormula_of_isSeparable
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F'] :
  Divisor.PushforwardNormFormula K F F' := by
  intro f hf D hD v
  classical
  have hNorm : v.ord (Algebra.norm F f) =
      ∑ w ∈ v.fiber F', (w.inertiaDeg F : ℤ) * w.ord f := by
    rw [Place.fiber_eq_fiberOver]
    exact Place.ord_norm_eq_sum_fiberOver_of_isSeparable v hf
  rw [Divisor.pushforward_apply, hNorm]
  calc
    ∑ w ∈ D.support, (if w.restrict F = v then D w * (w.inertiaDeg F : ℤ) else 0)
        = ∑ w ∈ D.support ∪ v.fiber F',
            (if w.restrict F = v then D w * (w.inertiaDeg F : ℤ) else 0) := by
          refine Finset.sum_subset Finset.subset_union_left fun w _ hw => ?_
          rw [Finsupp.notMem_support_iff.mp hw, zero_mul, ite_self]
    _ = ∑ w ∈ v.fiber F', (if w.restrict F = v then D w * (w.inertiaDeg F : ℤ) else 0) := by
          refine (Finset.sum_subset Finset.subset_union_right fun w _ hw => ?_).symm
          rw [ite_eq_right fun h => hw (Place.mem_fiber.mpr h)]
    _ = ∑ w ∈ v.fiber F', (w.inertiaDeg F : ℤ) * w.ord f := by
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [ite_eq_left (Place.mem_fiber.mp hw), hD w, mul_comm]

end AlgebraicCurve.Divisor

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_mul_mem_lSpace_add.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Adelic.Index

/-! Multiplication adds the divisor bounds of Riemann--Roch spaces. -/

namespace AlgebraicCurve

theorem mul_mem_lSpace_add {K : Type*} {F : Type*} [Field K] [Field F]
  [Algebra K F] {D E : Divisor K F} {f g : F}
    (hf : f ∈ LSpace D) (hg : g ∈ LSpace E) :
    f * g ∈ LSpace (D + E) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [zero_mul]; exact (LSpace _).zero_mem
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [mul_zero]; exact (LSpace _).zero_mem
  rw [mem_lSpace_iff_ord]
  refine Or.inr fun v => ?_
  rw [Finsupp.add_apply, neg_add, v.ord_mul hf0 hg0]
  exact add_le_add ((mem_lSpace_iff_ord.mp hf).resolve_left hf0 v)
    ((mem_lSpace_iff_ord.mp hg).resolve_left hg0 v)

end AlgebraicCurve

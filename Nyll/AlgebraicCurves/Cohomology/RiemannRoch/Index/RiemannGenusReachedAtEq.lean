/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_RiemannGenusReachedAt_eq_of_ge.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Genus.AdelicGenus
import Mathlib.Tactic.Linarith.Frontend

/-! # Stability after the Riemann genus is attained -/

namespace AlgebraicCurve

theorem RiemannGenusReachedAt.eq_of_ge
    {K F : Type*} [Field K] [Field F]
    [Algebra K F] [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {D : Divisor K F} (hD : D₀ ≤ D) :
    Divisor.degree D - ell D = γ - 1 := by
  have := finiteDimensional_lSpace (K := K) D
  have hge : Divisor.degree D₀ - (ell D₀ : ℤ) ≤ Divisor.degree D - ell D := by
    have := ell_sub_ell_le_degree_sub_degree (K := K) hD
    linarith
  exact le_antisymm (h.isMax D) (h.eq ▸ hge)

end AlgebraicCurve

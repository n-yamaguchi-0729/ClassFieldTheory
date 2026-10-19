/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_TranscendenceTower_degree_poleDivisor_eq_finrank.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Degree.PoleData
import Nyll.AlgebraicCurves.Divisors.Maps.Maps
import Nyll.AlgebraicCurves.Places.Ramification.SumRamificationIndexMulInertiaDeg

/-! # Degree of the coordinate pole divisor -/

namespace AlgebraicCurve

theorem TranscendenceTower.degree_poleDivisor_eq_finrank
    {K E F : Type*} [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
    [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]
    (T : TranscendenceTower K E F) :
    Divisor.degree T.poleDivisor = (Module.finrank E F : ℤ) := by
  have : SumRamificationInertia K E F :=
    ⟨fun v => Place.sum_ramificationIndex_mul_inertiaDeg v⟩
  have : FundamentalIdentity K E F := instFundamentalIdentityOfSumRamificationInertia
  rw [TranscendenceTower.poleDivisor, Divisor.degree_pullback, Divisor.degree_single,
    T.hvdeg, Nat.cast_one, one_mul, mul_one]

end AlgebraicCurve

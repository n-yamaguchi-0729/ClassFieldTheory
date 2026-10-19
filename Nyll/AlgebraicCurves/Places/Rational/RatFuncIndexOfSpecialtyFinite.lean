/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_indexOfSpecialtyFinite_of_ratFunc_tower.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Genus.AdelicGenus
import Nyll.AlgebraicCurves.Places.Rational.RatFuncStichtenothGenusExistsRatFuncTower

/-! A finite rational-function tower has a finite adelic quotient. -/

open AlgebraicCurve

theorem AlgebraicCurve.RationalFunctionField.indexOfSpecialtyFinite_of_ratFunc_tower
    (K : Type*) [Field K] (F : Type*) [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
    [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))] :
    IndexOfSpecialtyFinite K F := by
  obtain ⟨hne, hL0, γ, D₀, hD₀⟩ :=
    RationalFunctionField.stichtenothGenusExists_of_ratFunc_tower K F
  exact ⟨D₀, (indexOfSpecialty_eq_of_genusReached hD₀ D₀).1⟩

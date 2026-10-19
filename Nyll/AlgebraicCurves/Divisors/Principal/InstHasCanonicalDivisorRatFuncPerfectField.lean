/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_instHasCanonicalDivisorRatFuncPerfectField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


import Nyll.AlgebraicCurves.Differentials.Local.LocalGeometry
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.EssentialFiniteness

/-!
# Canonical divisors of the rational function field

The polynomial localization supplies essential finite type, so the general construction of
canonical divisors applies over every perfect base field.
-/

theorem AlgebraicCurve.instHasCanonicalDivisorRatFuncPerfectField (K : Type*) [Field K]
    [PerfectField K] [AlgebraicCurve.IsCurveOver K (RatFunc K)] :
    AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K) := by
  have : Algebra.EssFiniteType (Polynomial K) (RatFunc K) :=
    Algebra.EssFiniteType.of_isLocalization (RatFunc K) (nonZeroDivisors (Polynomial K))
  have : Algebra.EssFiniteType K (RatFunc K) :=
    Algebra.EssFiniteType.comp K (Polynomial K) (RatFunc K)
  exact AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver (K := K) (F := RatFunc K)

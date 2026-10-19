/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.Rational.Classification

/-!
# RationalFunctionField subsingleton setOf forall ne ofHeightOneSpectrum

The places of a rational function field outside the polynomial height-one spectrum form a
subsingleton.
-/

namespace AlgebraicCurve.RationalFunctionField

theorem subsingleton_setOf_forall_ne_ofHeightOneSpectrum {K : Type*} [Field K] :
    {v : Place K (RatFunc K) | ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
      v ≠ Place.ofHeightOneSpectrum w}.Subsingleton := by
  classical
  intro v hv v' hv'
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, h⟩ | h
  · exact absurd h (hv w)
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v' with ⟨w, h'⟩ | h'
  · exact absurd h' (hv' w)
  exact h.trans h'.symm

end AlgebraicCurve.RationalFunctionField

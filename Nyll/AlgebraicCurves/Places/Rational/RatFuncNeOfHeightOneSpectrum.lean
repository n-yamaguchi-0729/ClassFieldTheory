/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_exists_forall_ne_ofHeightOneSpectrum.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.Rational.Classification

/-!
# RationalFunctionField exists forall ne ofHeightOneSpectrum

A rational function field has a place outside the places arising from polynomial height-one
primes.
-/

namespace AlgebraicCurve.RationalFunctionField

theorem exists_forall_ne_ofHeightOneSpectrum {K : Type*} [Field K] :
    ∃ v : Place K (RatFunc K), ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
      v ≠ Place.ofHeightOneSpectrum w := by
  classical
  exact ⟨placeInfty K, placeInfty_ne_ofHeightOneSpectrum K⟩

end AlgebraicCurve.RationalFunctionField

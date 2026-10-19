/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_finrank_omegaSpace_eq_ell_canonical_sub_of_genusReached.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Differentials.Kaehler.Weil
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Index.IndexOfSpecialtyEqEllSub
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Duality.WeilDifferentialRankOne

/-! The dimension of Weil differentials is the dimension of the canonical space of sections. -/

open AlgebraicCurve KaehlerDifferential
open AlgebraicCurves.Cohomology.RiemannRoch.Proofs.WeilDifferentialRankOne

theorem _root_.AlgebraicCurve.finrank_omegaSpace_eq_ell_canonical_sub_of_genusReached {K : Type*}
  {F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [Nonempty (Place K F)]
  [FiniteDimensional K (LSpace (0 : Divisor K F))] [HasCanonicalDivisor (K := K) (F := F)] [∀ v :
  Place K F, v.DCoordGenerates] [HasCanonicalLocalResidueKStar K F]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (hWK : WeilKaehlerAgree K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) (D : Divisor K F) :
    Module.finrank K (omegaSpace (K := K) (F := F) D) = ell (canonicalDivisorOf hω - D) := by
  obtain ⟨hne, hmem, hmax⟩ := hWK hω
  rw [finrank_omegaSpace_eq_indexOfSpecialty]
  exact indexOfSpecialty_eq_ell_sub_of_rankOne_max
    (weilDifferentialRankOne_of_genusReached h) hmem hne hmax D

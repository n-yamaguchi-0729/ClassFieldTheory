/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_riemannGenusReached_of_stichtenothGenusExists.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Divisors.Principal.Canonical
import Nyll.AlgebraicCurves.Differentials.Kaehler.Weil
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Genus.AdelicGenus
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Duality.FinrankOmegaSpaceEqEllCanonicalSub
import Mathlib.Tactic.Linarith

/-! The attained Riemann genus agrees with the genus of a canonical divisor. -/

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.RiemannGenusReachedStichtenoth

noncomputable section

open _root_.AlgebraicCurve Module KaehlerDifferential

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section Identification

variable [IsCurveOver K F] [Nonempty (Place K F)]
  [FiniteDimensional K (LSpace (0 : Divisor K F))]
  [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  [HasCanonicalLocalResidueKStar K F]

theorem ell_canonicalDivisor_eq_stichtenothGenus
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (hWK : WeilKaehlerAgree K F) (hC : ConstantsAreBase K F)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    (ell (canonicalDivisorOf hω) : ℤ) = γ := by
  have hΩ0 := finrank_omegaSpace_eq_ell_canonical_sub_of_genusReached h hWK hω 0
  rw [sub_zero] at hΩ0
  have hi0 := (indexOfSpecialty_eq_of_genusReached h 0).2
  rw [← finrank_omegaSpace_eq_indexOfSpecialty, hΩ0, map_zero,
    ell_zero_eq_one_of_constantsAreBase hC] at hi0
  push_cast at hi0; linarith

theorem degree_canonicalDivisor_eq_of_genusReached
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (hWK : WeilKaehlerAgree K F) (hC : ConstantsAreBase K F)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    Divisor.degree (canonicalDivisorOf hω) = 2 * γ - 2 := by
  have hΩW := finrank_omegaSpace_eq_ell_canonical_sub_of_genusReached h hWK hω
    (canonicalDivisorOf hω)
  rw [sub_self] at hΩW
  have hiW := (indexOfSpecialty_eq_of_genusReached h (canonicalDivisorOf hω)).2
  rw [← finrank_omegaSpace_eq_indexOfSpecialty, hΩW,
    ell_zero_eq_one_of_constantsAreBase hC] at hiW
  have hℓW := ell_canonicalDivisor_eq_stichtenothGenus h hWK hC hω
  push_cast at hiW; linarith
omit [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  [HasCanonicalLocalResidueKStar K F] in
theorem stichtenothGenus_nonneg
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (hC : ConstantsAreBase K F) : 0 ≤ γ := by
  have hi0 := (indexOfSpecialty_eq_of_genusReached h 0).2
  rw [map_zero, ell_zero_eq_one_of_constantsAreBase hC] at hi0
  have h0 : (0 : ℤ) ≤ (indexOfSpecialty (0 : Divisor K F) : ℤ) := Int.natCast_nonneg _
  push_cast at hi0; linarith
omit [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
  [∀ v : Place K F, v.DCoordGenerates] [HasCanonicalLocalResidueKStar K F] in
theorem genus_eq_degree_div :
    ∃ (ω₀ : Ω[F⁄K]) (hω₀ : ω₀ ≠ 0),
      genus K F = (Divisor.degree (canonicalDivisorOf hω₀) + 2).toNat / 2 := by
  have hne : ∃ ω : Ω[F⁄K], ω ≠ 0 := exists_ne 0
  refine ⟨hne.choose, hne.choose_spec, ?_⟩
  rw [genus, dite_eq_left hne]

theorem stichtenothGenus_eq_genus
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (hWK : WeilKaehlerAgree K F) (hC : ConstantsAreBase K F) :
    γ = (genus K F : ℤ) := by
  obtain ⟨ω₀, hω₀, hgen⟩ := genus_eq_degree_div (K := K) (F := F)
  have hdeg := degree_canonicalDivisor_eq_of_genusReached h hWK hC hω₀
  have hγ0 := stichtenothGenus_nonneg h hC
  rw [hgen, hdeg]
  have h2 : (2 * γ - 2 + 2).toNat / 2 = γ.toNat := by omega
  rw [h2]
  exact (Int.toNat_of_nonneg hγ0).symm

end Identification

theorem _root_.AlgebraicCurve.riemannGenusReached_of_stichtenothGenusExists {K : Type*} {F :
  Type*} [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates] [HasCanonicalLocalResidueKStar K F]
    (hSG : StichtenothGenusExists K F)
    (hWK : WeilKaehlerAgree K F) (hC : ConstantsAreBase K F) :
    RiemannGenusReached K F (genus K F) := by
  obtain ⟨hne, hL0, γ, D₀, hD₀⟩ := hSG
  have : Nonempty (Place K F) := hne
  have : FiniteDimensional K (LSpace (0 : Divisor K F)) := hL0
  have hγeq := stichtenothGenus_eq_genus hD₀ hWK hC
  exact ⟨hne, hL0, D₀, hγeq ▸ hD₀⟩

end

end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.RiemannGenusReachedStichtenoth

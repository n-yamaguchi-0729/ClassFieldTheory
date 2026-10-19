/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_riemannGenusBounded_of_indexFinite.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Genus.AdelicGenus
import Mathlib.Tactic.Linarith

/-! A finite adelic quotient bounds the Riemann genus. -/

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.RiemannGenusBoundedIndexFinite

noncomputable section

open _root_.AlgebraicCurve Module
open AlgebraicCurves.Cohomology.RiemannRoch.Proofs
open IndexOfSpecialty_eq_of_genusReached.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem indexOfSpecialty_sub_of_ge [IsCurveOver K F] [Nonempty (Place K F)]
    {D₀ D : Divisor K F} (hD : D₀ ≤ D)
    [FiniteDimensional K (LSpace D)]
    [hfin : Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D₀)] :
    Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D) ∧
      (Divisor.degree D - ell D) - (Divisor.degree D₀ - ell D₀)
        = (indexOfSpecialty D₀ : ℤ) - (indexOfSpecialty D : ℤ) := by
  have hABsub : adeleBdd D₀ ⊔ globalSub K F ≤ adeleBdd D ⊔ globalSub K F :=
    sup_le_sup_right (adeleBdd_mono hD) _
  have hBCsub : adeleBdd D ⊔ globalSub K F ≤ adeleSpace K F :=
    adeleBdd_sup_globalSub_le_adeleSpace _
  obtain ⟨hfinBA, hdimBA⟩ := finrank_adeleBddSup_quotient (K := K) hD
  have := hfinBA
  have hfinCA : Module.Finite K (adeleSpace K F ⧸
      (adeleBdd D₀ ⊔ globalSub K F).comap (adeleSpace K F).subtype) := by
    rw [← adeleBddPrincipal_eq_comap]; exact hfin
  obtain ⟨hfinCB, _⟩ := IndexOfSpecialty_eq_of_genusReached.Submodule.finrank_quotient_chain'
    (A := adeleBdd D₀ ⊔ globalSub K F) (B := adeleBdd D ⊔ globalSub K F)
    (C := adeleSpace K F) hABsub hBCsub
  have hi0 : indexOfSpecialty D₀
      = finrank K (adeleSpace K F ⧸
        (adeleBdd D₀ ⊔ globalSub K F).comap (adeleSpace K F).subtype) := by
    rw [indexOfSpecialty_eq, adeleBddPrincipal_eq_comap]
  have hiD : indexOfSpecialty D
      = finrank K (adeleSpace K F ⧸
        (adeleBdd D ⊔ globalSub K F).comap (adeleSpace K F).subtype) := by
    rw [indexOfSpecialty_eq, adeleBddPrincipal_eq_comap]
  have := hfinCB
  obtain ⟨_, hdimCA⟩ := IndexOfSpecialty_eq_of_genusReached.Submodule.finrank_quotient_chain
    (A := adeleBdd D₀ ⊔ globalSub K F) (B := adeleBdd D ⊔ globalSub K F)
    (C := adeleSpace K F) hABsub hBCsub
  refine ⟨?_, ?_⟩
  · rw [show adeleBddPrincipal K F D
        = (adeleBdd D ⊔ globalSub K F).comap (adeleSpace K F).subtype
      from adeleBddPrincipal_eq_comap D]
    exact hfinCB
  · have hcast : (indexOfSpecialty D₀ : ℤ)
        = (indexOfSpecialty D : ℤ)
          + (finrank K (↥(adeleBdd D ⊔ globalSub K F)
              ⧸ (adeleBdd D₀ ⊔ globalSub K F).comap
                (adeleBdd D ⊔ globalSub K F).subtype) : ℤ) := by
      rw [hiD, hi0]; exact_mod_cast hdimCA
    linarith [hdimBA, hcast]

theorem degreeSub_ell_le_of_indexFinite [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {D₀ : Divisor K F}
    (hfin : Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D₀))
    (D : Divisor K F) :
    Divisor.degree D - ell D ≤ (Divisor.degree D₀ - ell D₀) + indexOfSpecialty D₀ := by
  have := hfin
  have := _root_.AlgebraicCurve.finiteDimensional_lSpace (K := K) (D ⊔ D₀)
  have hmono : Divisor.degree D - (ell D : ℤ)
      ≤ Divisor.degree (D ⊔ D₀) - ell (D ⊔ D₀) := by
    have h := _root_.AlgebraicCurve.ell_sub_ell_le_degree_sub_degree
      (K := K) (le_sup_left : D ≤ D ⊔ D₀)
    linarith
  obtain ⟨_, heq⟩ :=
    indexOfSpecialty_sub_of_ge (K := K) (le_sup_right : D₀ ≤ D ⊔ D₀)
  have hi0 : (0 : ℤ) ≤ indexOfSpecialty (D ⊔ D₀) := Int.natCast_nonneg _
  linarith

theorem _root_.AlgebraicCurve.riemannGenusBounded_of_indexFinite {K : Type*} {F : Type*} [Field K]
  [Field F] [Algebra K F] [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hfin : IndexOfSpecialtyFinite K F) :
    RiemannGenusBounded K F := by
  obtain ⟨D₀, hD₀⟩ := hfin
  exact ⟨(Divisor.degree D₀ - ell D₀) + indexOfSpecialty D₀,
    degreeSub_ell_le_of_indexFinite hD₀⟩

end

end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.RiemannGenusBoundedIndexFinite

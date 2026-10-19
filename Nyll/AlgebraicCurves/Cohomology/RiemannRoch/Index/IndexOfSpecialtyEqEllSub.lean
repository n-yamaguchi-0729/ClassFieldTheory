/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_indexOfSpecialty_eq_ell_sub_of_rankOne_max.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Duality.WeilDifferentialRankOne
import Mathlib.Tactic.Linarith

/-! The residue pairing identifies the index of specialty with a space of sections. -/

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.IndexOfSpecialtyEllSubRankOneMax

noncomputable section

open _root_.AlgebraicCurve
open AlgebraicCurves.Cohomology.RiemannRoch.Proofs.WeilDifferentialRankOne

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem residuePairing_surjective_of_rankOne_max [HasPrincipalDivisors K F]
    (hRankOne : WeilDifferentialRankOne K F)
    {W : Divisor K F} {φ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hφ0 : φ ≠ 0)
    (hWmax : ∀ E : Divisor K F, φ ∈ omegaSpace E → E ≤ W) (D : Divisor K F) :
    Function.Surjective (residuePairing K F W D hφ) := by
  rintro ⟨μ, hμD⟩
  have hφmem : φ ∈ weilDifferentialModule K F := omegaSpace_le_weilDifferentialModule W hφ
  have hμmem : μ ∈ weilDifferentialModule K F := omegaSpace_le_weilDifferentialModule D hμD
  obtain ⟨f, hf, -⟩ := hRankOne hφmem hφ0 hμmem
  rcases eq_or_ne f 0 with rfl | hf0
  · have hμ0 : (⟨μ, hμD⟩ : omegaSpace D) = 0 :=
      Subtype.ext (hf.trans (weilSmul_zero_left φ))
    exact ⟨0, (map_zero _).trans hμ0.symm⟩
  · obtain ⟨P, hPord, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
    have hPinv : ∀ v, (-P) v = v.ord f⁻¹ := fun v => by
      rw [Finsupp.neg_apply, hPord v, v.ord_inv]
    have hinv : weilSmul K F f⁻¹ μ = φ := by
      rw [hf, ← LinearMap.comp_apply, ← weilSmul_mul, mul_inv_cancel₀ hf0, weilSmul_one,
        LinearMap.id_apply]
    have hφD : φ ∈ omegaSpace (D + -P) := by
      rw [← hinv]; exact weilSmul_mem_omegaSpace_add (inv_ne_zero hf0) hPinv hμD
    have hDP : D + -P ≤ W := hWmax _ hφD
    have hfL : f ∈ LSpace (W - D) := by
      rw [mem_lSpace_iff_ord]; refine Or.inr fun v => ?_
      have hv := hDP v
      rw [Finsupp.add_apply, Finsupp.neg_apply, hPord v] at hv
      rw [Finsupp.sub_apply]; linarith
    exact ⟨⟨f, hfL⟩, Subtype.ext hf.symm⟩

theorem _root_.AlgebraicCurve.indexOfSpecialty_eq_ell_sub_of_rankOne_max {K F : Type*} [Field K]
  [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (hRankOne : WeilDifferentialRankOne K F)
    {W : Divisor K F} {φ : Module.Dual K ↥(adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hφ0 : φ ≠ 0)
    (hWmax : ∀ E : Divisor K F, φ ∈ omegaSpace E → E ≤ W) (D : Divisor K F) :
    indexOfSpecialty D = ell (W - D) := by
  rw [← finrank_omegaSpace_eq_indexOfSpecialty]
  exact (LinearEquiv.ofBijective (residuePairing K F W D hφ)
    ⟨residuePairing_injective W D hφ hφ0,
      residuePairing_surjective_of_rankOne_max hRankOne hφ hφ0 hWmax D⟩).finrank_eq.symm

end

end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.IndexOfSpecialtyEllSubRankOneMax

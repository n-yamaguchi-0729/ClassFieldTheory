/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_weilDifferentialRankOne_of_stichtenothGenusExists.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.SectionBounds
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Genus.AdelicGenus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring.RingNF

/-! Weil differentials have rank one when the Riemann genus is attained. -/

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.WeilDifferentialRankOne

noncomputable section

open _root_.AlgebraicCurve Module
open
  AlgebraicCurves.Cohomology.RiemannRoch.Proofs.IndexOfSpecialty_eq_of_genusReached.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem adeleSpaceMul_add [HasPrincipalDivisors K F] (f g : F) :
    adeleSpaceMul K F (f + g) = adeleSpaceMul K F f + adeleSpaceMul K F g := by
  refine LinearMap.ext fun α => Subtype.ext (funext fun v => ?_)
  simp only [adeleSpaceMul_coe, mulAdele_apply, LinearMap.add_apply, Submodule.coe_add,
    Pi.add_apply, add_mul]

theorem adeleSpaceMul_zero [HasPrincipalDivisors K F] :
    adeleSpaceMul K F (0 : F) = 0 := by
  refine LinearMap.ext fun α => Subtype.ext (funext fun v => ?_)
  simp only [adeleSpaceMul_coe, mulAdele_apply, zero_mul, LinearMap.zero_apply,
    Submodule.coe_zero, Pi.zero_apply]

theorem weilSmul_add_left [HasPrincipalDivisors K F] (f g : F)
    (φ : Module.Dual K (adeleSpace K F)) :
    weilSmul K F (f + g) φ = weilSmul K F f φ + weilSmul K F g φ := by
  ext α
  simp only [weilSmul_apply, adeleSpaceMul_add, LinearMap.add_apply, map_add]

theorem weilSmul_zero_left [HasPrincipalDivisors K F]
    (φ : Module.Dual K (adeleSpace K F)) :
    weilSmul K F (0 : F) φ = 0 := by
  ext α
  simp only [weilSmul_apply, adeleSpaceMul_zero, LinearMap.zero_apply, map_zero]

theorem weilSmul_neg_left [HasPrincipalDivisors K F] (f : F)
    (φ : Module.Dual K (adeleSpace K F)) :
    weilSmul K F (-f) φ = -weilSmul K F f φ := by
  have h := weilSmul_add_left (K := K) (F := F) f (-f) φ
  rw [add_neg_cancel, weilSmul_zero_left] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem weilSmul_sub_left [HasPrincipalDivisors K F] (f g : F)
    (φ : Module.Dual K (adeleSpace K F)) :
    weilSmul K F (f - g) φ = weilSmul K F f φ - weilSmul K F g φ := by
  rw [sub_eq_add_neg, weilSmul_add_left, weilSmul_neg_left, sub_eq_add_neg]

theorem weilSmul_eq_zero_iff_left [HasPrincipalDivisors K F]
    {f : F} {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ≠ 0) :
    weilSmul K F f φ = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ weilSmul_zero_left φ⟩
  by_contra hf
  exact hφ (weilSmul_injective hf (h.trans (map_zero (weilSmul K F f)).symm))

theorem weilSmul_left_injective [HasPrincipalDivisors K F]
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ≠ 0) :
    Function.Injective (fun f : F => weilSmul K F f φ) := by
  intro f g hfg
  have hsub : weilSmul K F (f - g) φ = 0 := by
    rw [weilSmul_sub_left, sub_eq_zero]; exact hfg
  exact sub_eq_zero.mp ((weilSmul_eq_zero_iff_left hφ).mp hsub)

variable (K F) in
/-- The sum of the two residue pairings on the product of their spaces of sections. -/
def doubleResiduePairing [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ μ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W) :
    LSpace (W - D) × LSpace (W - D) →ₗ[K] omegaSpace D :=
  (residuePairing K F W D hφ).coprod (residuePairing K F W D hμ)

theorem doubleResiduePairing_apply_coe [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ μ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W) (g h : LSpace (W - D)) :
    (doubleResiduePairing K F W D hφ hμ (g, h) : Module.Dual K (adeleSpace K F))
      = weilSmul K F (g : F) φ + weilSmul K F (h : F) μ := by
  simp only [doubleResiduePairing, LinearMap.coprod_apply, Submodule.coe_add,
    residuePairing_apply_coe]

theorem doubleResiduePairing_injective [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ μ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W)
    (hφ0 : φ ≠ 0) (hindep : ∀ f : F, μ ≠ weilSmul K F f φ) :
    Function.Injective (doubleResiduePairing K F W D hφ hμ) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨g, h⟩ heq
  have heq' : weilSmul K F (g : F) φ + weilSmul K F (h : F) μ = 0 := by
    have hcoe := congrArg Subtype.val heq
    rwa [doubleResiduePairing_apply_coe, Submodule.coe_zero] at hcoe
  rcases eq_or_ne (h : F) 0 with hh0 | hh0
  · rw [hh0, weilSmul_zero_left, add_zero] at heq'
    have hg0 : (g : F) = 0 := (weilSmul_eq_zero_iff_left hφ0).mp heq'
    exact Prod.ext (Subtype.ext hg0) (Subtype.ext hh0)
  · exfalso
    have hμeq : weilSmul K F (h : F) μ = -weilSmul K F (g : F) φ := by
      have h2 : weilSmul K F (h : F) μ + weilSmul K F (g : F) φ = 0 := by
        rw [add_comm]; exact heq'
      exact eq_neg_of_add_eq_zero_left h2
    have hLHS : weilSmul K F (h : F)⁻¹ (weilSmul K F (h : F) μ) = μ := by
      rw [← LinearMap.comp_apply, ← weilSmul_mul, mul_inv_cancel₀ hh0, weilSmul_one,
        LinearMap.id_apply]
    have hRHS : weilSmul K F (h : F)⁻¹ (-weilSmul K F (g : F) φ)
        = weilSmul K F (-(g : F) * (h : F)⁻¹) φ := by
      rw [map_neg, ← LinearMap.comp_apply, ← weilSmul_mul, neg_mul, weilSmul_neg_left]
    exact hindep (-(g : F) * (h : F)⁻¹) (by rw [← hLHS, hμeq, hRHS])

theorem two_mul_ell_le_indexOfSpecialty [HasPrincipalDivisors K F] (W D : Divisor K F)
    {φ μ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W)
    (hφ0 : φ ≠ 0) (hindep : ∀ f : F, μ ≠ weilSmul K F f φ)
    [Module.Finite K (omegaSpace (K := K) (F := F) D)]
    [Module.Finite K (LSpace (K := K) (F := F) (W - D))] :
    2 * ell (W - D) ≤ indexOfSpecialty D := by
  have hinj := doubleResiduePairing_injective W D hφ hμ hφ0 hindep
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod] at hle
  rw [← finrank_omegaSpace_eq_indexOfSpecialty, two_mul]
  exact hle


section ParametricRankOne

variable [IsCurveOver K F] [Nonempty (Place K F)]
  [FiniteDimensional K (LSpace (0 : Divisor K F))]


theorem exists_weilSmul_eq_of_genusReached
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {φ μ : Module.Dual K (adeleSpace K F)} {W : Divisor K F}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W) (hφ0 : φ ≠ 0) :
    ∃ f : F, μ = weilSmul K F f φ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨P⟩ := ‹Nonempty (Place K F)›
  set n : ℕ := 3 * γ.natAbs + 2 * (Divisor.degree W).natAbs + 4 with hn
  set D : Divisor K F := -Finsupp.single P (n : ℤ) with hD
  have hdegD : Divisor.degree D = -(n : ℤ) * (P.deg : ℤ) := by
    rw [hD, map_neg, Divisor.degree_single]; ring
  have hdegWD : Divisor.degree (W - D) = Divisor.degree W + (n : ℤ) * (P.deg : ℤ) := by
    rw [map_sub, hdegD]; ring
  have hPdeg1 : 1 ≤ (P.deg : ℤ) := by exact_mod_cast one_le_deg P
  have habsγ : -(|γ|) ≤ γ ∧ γ ≤ |γ| := ⟨neg_abs_le _, le_abs_self _⟩
  have habsW : -|Divisor.degree W| ≤ Divisor.degree W ∧
      Divisor.degree W ≤ |Divisor.degree W| := ⟨neg_abs_le _, le_abs_self _⟩
  have hn_ge : 3 * |γ| + 2 * |Divisor.degree W| + 4 ≤ (n : ℤ) := by
    rw [hn]; push_cast [Int.natCast_natAbs]; ring_nf; omega
  have hndegP : (n : ℤ) ≤ (n : ℤ) * (P.deg : ℤ) := by nlinarith [Int.natCast_nonneg n]
  have hellD : ell D = 0 := ell_eq_zero_of_degree_neg (by rw [hdegD]; nlinarith)
  have hiD : (indexOfSpecialty D : ℤ) = (n : ℤ) * (P.deg : ℤ) - 1 + γ := by
    have hidx := (indexOfSpecialty_eq_of_genusReached h D).2
    rw [hellD, hdegD] at hidx; push_cast at hidx; linarith
  have hlowerWD : Divisor.degree W + (n : ℤ) * (P.deg : ℤ) + 1 - γ
      ≤ (ell (W - D) : ℤ) := by
    have hlow := gate_riemannInequality_of_genusReached h (W - D)
    rw [hdegWD] at hlow; exact hlow
  have := omegaSpace_finite_of_genusReached h D
  have := _root_.AlgebraicCurve.finiteDimensional_lSpace (K := K) (W - D)
  have hdbl : (2 * ell (W - D) : ℤ) ≤ (indexOfSpecialty D : ℤ) := by
    exact_mod_cast two_mul_ell_le_indexOfSpecialty W D hφ hμ hφ0 hcon
  rw [hiD] at hdbl
  nlinarith [habsγ.1, habsγ.2, habsW.1, habsW.2]

theorem weilDifferentialRankOne_of_genusReached
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    WeilDifferentialRankOne K F := by
  intro φ hφmem hφ0 μ hμmem
  obtain ⟨W₁, hφW₁⟩ := mem_weilDifferentialModule_iff.mp hφmem
  obtain ⟨W₂, hμW₂⟩ := mem_weilDifferentialModule_iff.mp hμmem
  have hφW : φ ∈ omegaSpace (W₁ ⊓ W₂) := omegaSpace_antitone inf_le_left hφW₁
  have hμW : μ ∈ omegaSpace (W₁ ⊓ W₂) := omegaSpace_antitone inf_le_right hμW₂
  obtain ⟨f, hf⟩ := exists_weilSmul_eq_of_genusReached h hφW hμW hφ0
  exact ⟨f, hf, fun f' hf' => weilSmul_left_injective hφ0 (hf'.symm.trans hf)⟩

end ParametricRankOne

theorem _root_.AlgebraicCurve.weilDifferentialRankOne_of_stichtenothGenusExists {K F : Type*}
  [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    (h : StichtenothGenusExists K F) : WeilDifferentialRankOne K F := by
  obtain ⟨hne, hfin, γ, D₀, hγ⟩ := h
  have : Nonempty (Place K F) := hne
  have : FiniteDimensional K (LSpace (0 : Divisor K F)) := hfin
  intro φ hφ hφ0 μ hμ
  exact weilDifferentialRankOne_of_genusReached hγ hφ hφ0 hμ

end

end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.WeilDifferentialRankOne

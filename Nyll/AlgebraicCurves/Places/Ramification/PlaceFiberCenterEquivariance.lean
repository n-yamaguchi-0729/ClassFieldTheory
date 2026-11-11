/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
public import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
public import Nyll.AlgebraicCurves.Places.Restriction.RestrictionComposition
public import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Equivariance of the actual place–normalization-prime correspondence

The existing fiber center carries the actual field action to the prescribed
normalization action. Consequently the two literal stabilizer conditions agree.
The valuation calculation is extracted from the existing place transitivity proof.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain
open scoped Pointwise

namespace AlgebraicCurve.Place

variable {k F L : Type*} [Field k] [Field F] [Field L]
  [Algebra k F] [Algebra k L] [Algebra F L] [IsScalarTower k F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L]

private theorem ord_smul_eq_for_fiber
    (g : SemilinearAut k L) (w : Place k L) (x : L) :
    (g • w).ord x = w.ord (g⁻¹ • x) := by
  conv_lhs => rw [← smul_inv_smul g x]
  exact SemilinearAut.ord_smul g w (g⁻¹ • x)

variable (v : Place k F)

local instance fiberNormalizationAction :
    MulSemiringAction Gal(L/F) (integralClosureAt L v) :=
  IsIntegralClosure.MulSemiringAction v.toValuationSubring F L (integralClosureAt L v)

/-- The center of the translated place is the translated normalization prime. -/
theorem fiberCenter_ofAlgAut_smul_asIdeal
    (w : Place k L) (hw : w.restrict F = v) (σ : Gal(L/F)) :
    (fiberCenter L v ((restrict_ofAlgAut_smul σ w).trans hw)).asIdeal =
      σ • (fiberCenter L v hw).asIdeal := by
  apply Ideal.ext
  intro c
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  by_cases hc : c = 0
  · rw [hc, smul_zero]
    exact iff_of_true (Ideal.zero_mem _) (Ideal.zero_mem _)
  have hc' : σ⁻¹ • c ≠ 0 :=
    fun h0 => hc (by simpa using congrArg (σ • ·) h0)
  rw [mem_fiberCenter_iff_ord_pos _ hc,
    mem_fiberCenter_iff_ord_pos _ hc', ord_smul_eq_for_fiber,
    SemilinearAut.inv_smul_def, SemilinearAut.toRingAut_ofAlgAut]
  have key :
      algebraMap (integralClosureAt L v) L (σ⁻¹ • c) =
        ((σ.restrictScalars k : L ≃+* L)).symm
          (algebraMap (integralClosureAt L v) L c) := by
    rw [show σ⁻¹ • c =
        galRestrict v.toValuationSubring F L (integralClosureAt L v) σ⁻¹ c from rfl,
      algebraMap_galRestrict_apply, AlgEquiv.aut_inv]
    rfl
  rw [key]

/-- Stabilizing the literal fiber-center ideal is equivalent to fixing its place. -/
theorem fiberCenter_stabilizer_iff
    (w : Place k L) (hw : w.restrict F = v) (σ : Gal(L/F)) :
    σ • (fiberCenter L v hw).asIdeal = (fiberCenter L v hw).asIdeal ↔
      SemilinearAut.ofAlgAut (σ.restrictScalars k) • w = w := by
  have heq := fiberCenter_ofAlgAut_smul_asIdeal v w hw σ
  constructor
  · intro h
    apply eq_of_fiberCenter_eq ((restrict_ofAlgAut_smul σ w).trans hw) hw
    apply HeightOneSpectrum.ext
    exact heq.trans h
  · intro h
    have hfiber :
        (⟨SemilinearAut.ofAlgAut (σ.restrictScalars k) • w,
          (restrict_ofAlgAut_smul σ w).trans hw⟩ :
          {z : Place k L // z.restrict F = v}) = ⟨w, hw⟩ := Subtype.ext h
    have hc := congrArg
      (fun z : {z : Place k L // z.restrict F = v} =>
        ((fiberEquiv L v) z).asIdeal) hfiber
    exact heq.symm.trans hc

/-- The prime-to-place correspondence identifies the two stabilizer conditions. -/
theorem placeOfPrime_stabilizer_iff
    (P : HeightOneSpectrum (integralClosureAt L v)) (σ : Gal(L/F)) :
    σ • P.asIdeal = P.asIdeal ↔
      SemilinearAut.ofAlgAut (σ.restrictScalars k) • placeOfPrime P =
        placeOfPrime P := by
  simpa only [fiberCenter_placeOfPrime] using
    fiberCenter_stabilizer_iff v (placeOfPrime P) (restrict_placeOfPrime P) σ

end AlgebraicCurve.Place

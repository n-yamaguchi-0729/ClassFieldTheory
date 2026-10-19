/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantExtension
import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardAction

/-!
# Semilinear equivariance with changing constants

Extend the valuation-ring and ramification arguments from the semilinear
restriction lemmas to two different constant fields. Consequently actual
constant-field pullback commutes with intertwining field automorphisms.
-/

noncomputable section

namespace AlgebraicCurve.SemilinearAut

open scoped Pointwise

attribute [local instance]
  instMulSemiringActionSubtypeProdRingAutMemSubgroup
  instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor

variable {k E K L : Type*} [Field k] [Field E] [Field K] [Field L]
    [Algebra k K] [Algebra E L] [Algebra K L]
    {g : SemilinearAut k K} {h : SemilinearAut E L}

/-- Intertwining of the field actions also intertwines their inverses. -/
theorem intertwines_constants_inv
    (hc : ∀ x : K, h • algebraMap K L x = algebraMap K L (g • x)) (x : K) :
    h⁻¹ • algebraMap K L x = algebraMap K L (g⁻¹ • x) := by
  rw [inv_smul_eq_iff, hc, smul_inv_smul]

/-- Orders transform naturally even when the constant fields differ. -/
theorem ord_constants_smul
    (hc : ∀ x : K, h • algebraMap K L x = algebraMap K L (g • x))
    (w : Place E L) (x : K) :
    (h • w).ord (algebraMap K L x) = w.ord (algebraMap K L (g⁻¹ • x)) := by
  have hx : algebraMap K L x = h • algebraMap K L (g⁻¹ • x) := by
    rw [hc, smul_inv_smul]
  rw [hx]
  exact ord_smul h w _

variable [Algebra k E] [Algebra k L] [IsScalarTower k E L]

/-- Ramification indices are unchanged by compatible actions on both fields. -/
theorem ramificationIndex_constants_smul
    (hc : ∀ x : K, h • algebraMap K L x = algebraMap K L (g • x))
    (w : Place E L) :
    ((h • w).forgetConstants (K := k)).ramificationIndex K =
      (w.forgetConstants (K := k)).ramificationIndex K := by
  unfold Place.ramificationIndex
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨x, hx, hxord⟩
    refine ⟨g⁻¹ • x, by rwa [ne_eq, smul_eq_zero_iff_eq], ?_⟩
    exact (ord_constants_smul hc w x).symm.trans hxord
  · rintro ⟨x, hx, hxord⟩
    refine ⟨g • x, by rwa [ne_eq, smul_eq_zero_iff_eq], ?_⟩
    change (h • w).ord (algebraMap K L (g • x)) = _
    rw [ord_constants_smul hc, inv_smul_smul]
    exact hxord

variable [IsScalarTower k K L] [Algebra.IsIntegral K L]

/-- Restriction with changing constants intertwines compatible semilinear actions. -/
theorem restrictConstants_smul
    (hc : ∀ x : K, h • algebraMap K L x = algebraMap K L (g • x))
    (w : Place E L) :
    Place.restrictConstants K (K := k) (h • w) =
      g • Place.restrictConstants K (K := k) w := by
  apply Place.ext
  rw [Place.restrictConstants_toValuationSubring, smul_toValuationSubring,
    smul_toValuationSubring, Place.restrictConstants_toValuationSubring]
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_comap,
    intertwines_constants_inv hc]

variable [HasPrincipalDivisors E L]

/-- Pullback of actual divisors intertwines semilinear actions over different constants. -/
theorem pullbackConstants_smul
    (hc : ∀ x : K, h • algebraMap K L x = algebraMap K L (g • x))
    (D : Divisor k K) :
    Divisor.pullbackConstants E L (g • D) = h • Divisor.pullbackConstants E L D := by
  ext w
  rw [Divisor.pullbackConstants_apply, divisor_smul_apply, divisor_smul_apply,
    Divisor.pullbackConstants_apply,
    ramificationIndex_constants_smul (intertwines_constants_inv hc),
    restrictConstants_smul (intertwines_constants_inv hc)]

/-- Pullback of actual Picard classes intertwines the corresponding semilinear actions. -/
theorem baseChange_smul
    (hc : ∀ x : K, h • algebraMap K L x = algebraMap K L (g • x))
    (x : Pic k K) :
    Pic.baseChange k E K L (g • x) = h • Pic.baseChange k E K L x := by
  obtain ⟨D, rfl⟩ := H1Gm.mk_surjective x
  change H1Gm.mk (Divisor.pullbackConstants E L (g • D)) =
    H1Gm.mk (h • Divisor.pullbackConstants E L D)
  rw [pullbackConstants_smul hc]

end AlgebraicCurve.SemilinearAut

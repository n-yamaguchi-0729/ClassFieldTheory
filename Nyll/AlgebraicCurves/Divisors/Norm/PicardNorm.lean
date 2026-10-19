/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardAction
import Nyll.AlgebraicCurves.Divisors.Norm.PushforwardNormFormulaSeparable
import Nyll.AlgebraicCurves.Divisors.Norm.SumGaloisSmulEqPullbackPushforward

/-!
# The actual norm on full Picard groups

Divisor pushforward descends to Picard groups by the proved field-norm formula
for principal divisors. Its pullback in a Galois extension is the sum of the
actual conjugate classes.
-/

noncomputable section

namespace AlgebraicCurve.Pic

attribute [local instance]
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [HasPrincipalDivisors k L]

/-- Pullback of full divisor classes along the actual field inclusion. -/
def pullback : Pic k K →+ Pic k L :=
  QuotientAddGroup.map _ _ (Divisor.pullback L) (fun _ hD => Divisor.isPrincipal_pullback hD)

/-- Picard pullback is computed on divisor representatives. -/
theorem pullback_mk (D : Divisor k K) :
    pullback (L := L) (H1Gm.mk D) = H1Gm.mk (Divisor.pullback L D) := rfl

variable [Algebra.IsSeparable K L]

/-- The norm of divisor classes, defined by actual divisor pushforward. -/
def norm : Pic k L →+ Pic k K :=
  QuotientAddGroup.map _ _ (Divisor.pushforward K) (fun _ hD =>
    Divisor.isPrincipal_pushforward_of_normFormula
      Divisor.pushforwardNormFormula_of_isSeparable hD)

/-- The Picard norm is computed by the pushforward of an actual representative. -/
theorem norm_mk (D : Divisor k L) :
    norm (K := K) (H1Gm.mk D) = H1Gm.mk (Divisor.pushforward K D) := rfl

/-- The actual Picard norm preserves degree measured over the same constant field. -/
theorem degree_norm [HasPrincipalDivisors k K] (x : Pic k L) :
    H1Gm.degree k K (norm (K := K) x) = H1Gm.degree k L x := by
  obtain ⟨D, rfl⟩ := H1Gm.mk_surjective x
  exact Divisor.degree_pushforward D

/-- Pulling an actual norm back gives the sum over the actual Galois group. -/
theorem pullback_norm_eq_sum [IsGalois K L] (x : Pic k L) :
    pullback (L := L) (norm (K := K) x) =
      ∑ g : L ≃ₐ[K] L, SemilinearAut.ofAlgAut (g.restrictScalars k) • x := by
  obtain ⟨D, rfl⟩ := H1Gm.mk_surjective x
  change H1Gm.mk (Divisor.pullback L (Divisor.pushforward K D)) = _
  rw [← Divisor.sum_galois_smul_eq_pullback_pushforward]
  change (QuotientAddGroup.mk' Divisor.principal)
    (∑ g : L ≃ₐ[K] L, SemilinearAut.ofAlgAut (g.restrictScalars k) • D) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun g _ => (SemilinearAut.pic_smul_mk _ D).symm)

end AlgebraicCurve.Pic

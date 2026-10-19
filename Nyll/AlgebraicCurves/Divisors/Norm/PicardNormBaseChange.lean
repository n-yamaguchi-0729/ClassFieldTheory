/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Norm.PicardNorm
import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantBaseChangeTower
import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantSemilinear
import Nyll.GaloisCohomology.Cyclic.GeneratorSum

/-!
# Actual norms after geometric base change

Compose actual Picard pullbacks in a tower and express the pullback of a norm
as a cyclic Frobenius sum whenever an actual Galois generator extends geometrically.
-/

noncomputable section

namespace AlgebraicCurve.Pic

attribute [local instance] SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup

variable {k Ω K L F : Type*} [Field k] [Field Ω] [Field K] [Field L] [Field F]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [HasPrincipalDivisors k L]

/-- Constant-field pullback with unchanged constants is ordinary Picard pullback. -/
theorem baseChange_self (x : Pic k K) :
    baseChange k k K L x = pullback (L := L) x := by
  obtain ⟨D, rfl⟩ := H1Gm.mk_surjective x
  apply congrArg H1Gm.mk
  ext w
  rw [Divisor.pullbackConstants_apply, Divisor.pullback_apply]
  rfl

variable [Algebra k Ω] [Algebra Ω F] [Algebra k F] [IsScalarTower k Ω F]
    [Algebra K F] [Algebra L F]
    [IsScalarTower k K F] [IsScalarTower k L F] [IsScalarTower K L F]
    [Algebra.IsIntegral K F] [Algebra.IsIntegral L F] [HasPrincipalDivisors Ω F]

/-- Ordinary finite Picard pullback composes with geometric base change. -/
theorem baseChange_pullback (x : Pic k K) :
    baseChange k Ω L F (pullback (L := L) x) = baseChange k Ω K F x := by
  rw [← baseChange_self]
  exact baseChange_tower x

variable [IsGalois K L]

/-- Geometric pullback of an actual cyclic norm is the full sum of powers of its generator. -/
theorem baseChange_norm_eq_sum (g : L ≃ₐ[K] L) (hg : Subgroup.zpowers g = ⊤)
    (φ : SemilinearAut Ω F)
    (hc : ∀ y : L, φ • algebraMap L F y = algebraMap L F (g y)) (x : Pic k L) :
    baseChange k Ω K F (norm (K := K) x) =
      ∑ i ∈ Finset.range (orderOf g), φ ^ i • baseChange k Ω L F x := by
  rw [← baseChange_pullback (k := k) (Ω := Ω) (K := K) (L := L) (F := F),
    pullback_norm_eq_sum, map_sum,
    CyclicAction.sum_eq_sum_range_generator g hg]
  apply Finset.sum_congr rfl
  intro i hi
  clear hi
  apply SemilinearAut.baseChange_smul
  intro y
  change φ ^ i • algebraMap L F y = algebraMap L F ((g ^ i) y)
  induction i with
  | zero => rw [pow_zero, pow_zero, one_smul]; rfl
  | succ i ih =>
    rw [pow_succ', pow_succ', mul_smul, AlgEquiv.mul_apply, ih, hc]

end AlgebraicCurve.Pic

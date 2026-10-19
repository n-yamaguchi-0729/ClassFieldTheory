/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTower
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.AlgEquiv

/-!
# Equivariance of idele inclusion

Compatible automorphisms of a finite separable extension act compatibly on the
actual places and on their completions. Equality of the completed maps follows
from equality on the dense original field. Thus inclusion of ideles, and its
quotient on idele classes, intertwines simultaneous automorphisms of both fields.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place Pointwise

namespace FunctionField.IdeleGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

omit [IsScalarTower k K L] [FiniteDimensional K L] in
/-- Compatibility of field automorphisms is preserved by inversion. -/
theorem semilinear_compatible_inv (σ : SemilinearAut k L) (τ : SemilinearAut k K)
    (h : ∀ x : K, σ • algebraMap K L x = algebraMap K L (τ • x)) (x : K) :
    σ⁻¹ • algebraMap K L x = algebraMap K L (τ⁻¹ • x) := by
  apply (MulAction.injective σ)
  change σ • (σ⁻¹ • algebraMap K L x) = σ • algebraMap K L (τ⁻¹ • x)
  rw [smul_inv_smul, h, smul_inv_smul]

/-- Restriction of actual places intertwines compatible automorphisms. -/
theorem restrict_semilinear_smul_of_compatible
    (σ : SemilinearAut k L) (τ : SemilinearAut k K)
    (h : ∀ x : K, σ • algebraMap K L x = algebraMap K L (τ • x)) (w : Place k L) :
    (σ • w).restrict K = τ • w.restrict K := by
  apply Place.ext
  ext x
  rw [Place.restrict_toValuationSubring,
    SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_comap,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    Place.restrict_toValuationSubring, ValuationSubring.mem_comap]
  change σ⁻¹ • algebraMap K L x ∈ w.toValuationSubring ↔
    algebraMap K L (τ⁻¹ • x) ∈ w.toValuationSubring
  rw [semilinear_compatible_inv σ τ h]

/-- The square of actual completion maps for compatible field automorphisms
commutes by density of the original base field. -/
theorem completionMapOver_semilinear_compatible
    (σ : SemilinearAut k L) (τ : SemilinearAut k K)
    (h : ∀ x : K, σ • algebraMap K L x = algebraMap K L (τ • x))
    (v : Place k K) (w : Place k L) (hw : w.restrict K = v)
    (x : v.adicCompletion) :
    placeCompletionRingEquiv σ w
        (completionMapOver v w hw x) =
      completionMapOver (τ • v) (σ • w)
        ((restrict_semilinear_smul_of_compatible σ τ h w).trans
          (congrArg (fun u : Place k K => τ • u) hw))
        (placeCompletionRingEquiv τ v x) := by
  have heq : (fun x : v.adicCompletion =>
      placeCompletionRingEquiv σ w
        (completionMapOver v w hw x)) =
      (fun x : v.adicCompletion =>
        completionMapOver (τ • v) (σ • w)
          ((restrict_semilinear_smul_of_compatible σ τ h w).trans
            (congrArg (fun u : Place k K => τ • u) hw))
          (placeCompletionRingEquiv τ v x)) := by
    apply (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap
      K v.heightOneSpectrum).equalizer
    · exact (continuous_placeCompletionRingEquiv _ w).comp
        (continuous_completionMapOver v w hw)
    · exact (continuous_completionMapOver _ _ _).comp
        (continuous_placeCompletionRingEquiv _ v)
    · funext y
      simp only [Function.comp_apply, completionMapOver_algebraMap,
        placeCompletionRingEquiv_algebraMap]
      rw [h]
  exact congrFun heq x

variable [Algebra.IsSeparable K L]

/-- Actual idele inclusion is equivariant for compatible automorphisms of
the base and extension fields. -/
theorem baseChange_semilinear_smul (σ : SemilinearAut k L) (τ : SemilinearAut k K)
    (h : ∀ x : K, σ • algebraMap K L x = algebraMap K L (τ • x))
    (a : IdeleGroup k K) :
    baseChange (k := k) (K := K) (L := L) (τ • a) =
      σ • baseChange (k := k) (K := K) (L := L) a := by
  apply IdeleGroup.ext
  intro w
  apply Units.ext
  change (baseChange (k := k) (K := K) (L := L)
      (τ • a) w : w.adicCompletion) =
    (placeCompletionRingEquiv σ⁻¹ w).symm
      (baseChange (k := k) (K := K) (L := L) a (σ⁻¹ • w))
  apply (placeCompletionRingEquiv σ⁻¹ w).injective
  rw [RingEquiv.apply_symm_apply]
  have hc := completionMapOver_semilinear_compatible σ⁻¹ τ⁻¹
    (semilinear_compatible_inv σ τ h) (w.restrict K) w rfl
    ((τ • a) (w.restrict K))
  rw [completionMapOver_apply_baseChange] at hc
  change placeCompletionRingEquiv σ⁻¹ w
      (baseChange (k := k) (K := K) (L := L)
        (τ • a) w) =
    completionMapOver (τ⁻¹ • w.restrict K) (σ⁻¹ • w) _
      (placeCompletionRingEquiv τ⁻¹ (w.restrict K)
        ((placeCompletionRingEquiv τ⁻¹ (w.restrict K)).symm
          (a (τ⁻¹ • w.restrict K)))) at hc
  rw [RingEquiv.apply_symm_apply, completionMapOver_apply_baseChange] at hc
  exact hc

/-- Actual idele inclusion intertwines compatible algebra automorphisms. -/
theorem baseChange_algAut_smul (σ : L ≃ₐ[k] L) (τ : K ≃ₐ[k] K)
    (h : ∀ x : K, σ (algebraMap K L x) = algebraMap K L (τ x))
    (a : IdeleGroup k K) :
    baseChange (k := k) (K := K) (L := L) (SemilinearAut.ofAlgAut τ • a) =
      SemilinearAut.ofAlgAut σ • baseChange (k := k) (K := K) (L := L) a :=
  baseChange_semilinear_smul (SemilinearAut.ofAlgAut σ) (SemilinearAut.ofAlgAut τ) h a

end FunctionField.IdeleGroup

namespace FunctionField.IdeleClassGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- The simultaneous-automorphism equivariance of actual idele inclusion
descends through the principal-idele quotients. -/
theorem baseChange_algAut_smul (σ : L ≃ₐ[k] L) (τ : K ≃ₐ[k] K)
    (h : ∀ x : K, σ (algebraMap K L x) = algebraMap K L (τ x))
    (c : IdeleClassGroup k K) :
    baseChange (k := k) (K := K) (L := L) (SemilinearAut.ofAlgAut τ • c) =
      SemilinearAut.ofAlgAut σ • baseChange (k := k) (K := K) (L := L) c := by
  obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := K) c
  rw [smul_mk, baseChange_mk, baseChange_mk, smul_mk,
    IdeleGroup.baseChange_algAut_smul σ τ h]

end FunctionField.IdeleClassGroup

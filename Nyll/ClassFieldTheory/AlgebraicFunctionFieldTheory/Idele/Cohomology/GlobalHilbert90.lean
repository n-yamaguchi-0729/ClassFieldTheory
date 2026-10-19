/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.OrbitActions
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.DecompositionHilbert90
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormCohomology
import Nyll.ClassFieldTheory.Algebra.RestrictedProduct.Cohomology
import Nyll.ProCGroups.InducedFunctions.Cocycle
import Nyll.AlgebraicCurves.Places.Ramification.FiniteRamification

/-!
# Hilbert 90 for the actual all-place idele group

Local decomposition-group Hilbert 90 gives primitives on each finite place
fiber through the actual induced-module comparison. Outside the finite set of
ramified places these primitives can be chosen integral. Restricted-product
gluing then gives an actual idele primitive for every finite-Galois cocycle.
For a cyclic extension this identifies the actual idele norm kernel with the
augmentation image and proves vanishing of its Tate H⁻¹.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place RestrictedProduct

namespace FunctionField.IdeleGroup

open ProCGroups.InducedFunctions
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The actual induced-module comparison sends a fiber cocycle to an induced cocycle. -/
theorem fiber_isMulCocycle_induced (w : Place k L)
    (f : (L ≃ₐ[K] L) → FiberUnits (L := L) (w.restrict K))
    (hf : groupCohomology.IsMulCocycle₁ f) :
    groupCohomology.IsMulCocycle₁ (fun σ => fiberInducedEquiv (K := K) w (f σ)) := by
  intro σ τ
  change fiberInducedEquiv (K := K) w (f (σ * τ)) =
    σ • fiberInducedEquiv (K := K) w (f τ) * fiberInducedEquiv (K := K) w (f σ)
  rw [hf σ τ, map_mul, fiberInducedEquiv_smul]

/-- Every cocycle in the actual completed fiber has an actual fiber primitive. -/
theorem fiber_isMulCoboundary_of_isMulCocycle (v : Place k K)
    (f : (L ≃ₐ[K] L) → FiberUnits (L := L) v)
    (hf : groupCohomology.IsMulCocycle₁ f) :
    groupCohomology.IsMulCoboundary₁ f := by
  obtain ⟨w, rfl⟩ := Place.exists_restrict_eq (M := L) v
  let e := fiberInducedEquiv (K := K) w
  have hfi := fiber_isMulCocycle_induced (K := K) w f hf
  have hfe := induced_isMulCocycle_restrict_evaluation
    (decompositionGroup (K := K) w) (fun σ => e (f σ)) hfi
  have hbe := decomposition_isMulCoboundary_of_isMulCocycle (K := K) w _ hfe
  obtain ⟨b, hb⟩ := induced_isMulCoboundary_of_evaluation
    (decompositionGroup (K := K) w) (fun σ => e (f σ)) hfi hbe
  refine ⟨e.symm b, fun σ => e.injective ?_⟩
  rw [map_div, fiberInducedEquiv_smul, e.apply_symm_apply]
  exact hb σ

/-- If every place in a fiber is unramified, every integral actual fiber cocycle
has an integral primitive. -/
theorem exists_integral_fiber_coboundary_of_ramificationIndex_eq_one
    (v : Place k K)
    (he : ∀ w : Place k L, w.restrict K = v → w.ramificationIndex K = 1)
    (f : (L ≃ₐ[K] L) → FiberUnits (L := L) v)
    (hf : groupCohomology.IsMulCocycle₁ f)
    (hfint : ∀ σ : L ≃ₐ[K] L, f σ ∈ fiberIntegralUnits (L := L) v) :
    ∃ b : FiberUnits (L := L) v, b ∈ fiberIntegralUnits (L := L) v ∧
      ∀ σ : L ≃ₐ[K] L, (σ • b) / b = f σ := by
  obtain ⟨w, rfl⟩ := Place.exists_restrict_eq (M := L) v
  let e := fiberInducedEquiv (K := K) w
  have hfi := fiber_isMulCocycle_induced (K := K) w f hf
  have hfe := induced_isMulCocycle_restrict_evaluation
    (decompositionGroup (K := K) w) (fun σ => e (f σ)) hfi
  obtain ⟨b, hbint, hb⟩ :=
    exists_integral_decomposition_coboundary_of_ramificationIndex_eq_one
      (K := K) w (he w rfl) _ hfe
  let c := inducedCocyclePrimitive (decompositionGroup (K := K) w)
    (fun σ => e (f σ)) hfi b hb
  refine ⟨e.symm c, ?_, fun σ => e.injective ?_⟩
  · apply (fiberInducedEquiv_integral_iff (K := K) w (e.symm c)).mp
    rw [e.apply_symm_apply]
    intro σ
    change inducedEvaluation (decompositionGroup (K := K) w) (e (f σ)) * b ∈
      w.adicCompletionIntegers.units
    exact (w.adicCompletionIntegers.units).mul_mem
      ((fiberInducedEquiv_integral_iff (K := K) w (f σ)).mpr (hfint σ) 1) hbint
  · rw [map_div, fiberInducedEquiv_smul, e.apply_symm_apply]
    exact inducedCocyclePrimitive_coboundary
      (decompositionGroup (K := K) w) (fun σ => e (f σ)) hfi b hb σ

variable [HasPrincipalDivisors k L]

/-- Almost every base fiber admits integral primitives for its integral cocycles. -/
theorem eventually_exists_integral_fiber_coboundary :
    ∀ᶠ v : Place k K in Filter.cofinite,
      ∀ f : (L ≃ₐ[K] L) → FiberUnits (L := L) v,
        groupCohomology.IsMulCocycle₁ f →
        (∀ σ : L ≃ₐ[K] L, f σ ∈ fiberIntegralUnits (L := L) v) →
        ∃ b : FiberUnits (L := L) v, b ∈ fiberIntegralUnits (L := L) v ∧
          ∀ σ : L ≃ₐ[K] L, (σ • b) / b = f σ := by
  obtain ⟨S, hS⟩ :=
    exists_finset_forall_restrict_not_mem_ramificationIndex_eq_one_of_isSeparable
      (K := k) (F := K) (F' := L)
  have haway : ∀ᶠ v : Place k K in Filter.cofinite, v ∉ S :=
    S.finite_toSet.compl_mem_cofinite
  apply haway.mono
  intro v hv f hf hfint
  apply exists_integral_fiber_coboundary_of_ramificationIndex_eq_one v ?_ f hf hfint
  intro w hw
  exact hS w (by simpa only [hw] using hv)

/-- Every multiplicative cocycle of the actual finite-Galois action on all-place
ideles is an actual idele coboundary. -/
theorem isMulCoboundary_of_isMulCocycle
    (f : (L ≃ₐ[K] L) → IdeleGroup k L)
    (hf : groupCohomology.IsMulCocycle₁ f) :
    groupCohomology.IsMulCoboundary₁ f := by
  let e := groupByPlace (k := k) (K := K) (L := L)
  have hfg : groupCohomology.IsMulCocycle₁ (fun σ => e (f σ)) := by
    intro σ τ
    change e (f (σ * τ)) = σ • e (f τ) * e (f σ)
    rw [hf σ τ, map_mul, groupByPlace_smul]
  obtain ⟨b, hb⟩ :=
    RestrictedProduct.Cohomology.isMulCoboundary_of_local_and_eventual_integral
      (fiberRestrictedProduct_smul_apply (k := k) (K := K) (L := L))
      (fiber_isMulCoboundary_of_isMulCocycle (k := k) (K := K) (L := L))
      (eventually_exists_integral_fiber_coboundary (k := k) (K := K) (L := L))
      (fun σ => e (f σ)) hfg
  refine ⟨e.symm b, fun σ => e.injective ?_⟩
  rw [map_div, groupByPlace_smul, e.apply_symm_apply]
  exact hb σ

/-- For an actual cyclic extension, an idele of Tate norm one is a coboundary. -/
theorem normKernel_le_augmentationSubgroup (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    normKernelSubgroup (L ≃ₐ[K] L) (IdeleGroup k L) ≤
      augmentationSubgroup (L ≃ₐ[K] L) (IdeleGroup k L) σ := by
  intro a ha
  obtain ⟨f, hf, hfa⟩ := CyclicCohomology.exists_mulCocycle_of_tateNorm_eq_one σ hσ a ha
  obtain ⟨b, hb⟩ := isMulCoboundary_of_isMulCocycle f hf
  refine ⟨b, ?_⟩
  change σ • b * b⁻¹ = a
  simpa only [div_eq_mul_inv] using (hb σ).trans hfa

/-- The actual cyclic idele norm kernel is exactly its augmentation image. -/
theorem normKernel_eq_augmentationSubgroup (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    normKernelSubgroup (L ≃ₐ[K] L) (IdeleGroup k L) =
      augmentationSubgroup (L ≃ₐ[K] L) (IdeleGroup k L) σ :=
  le_antisymm (normKernel_le_augmentationSubgroup σ hσ)
    (augmentationSubgroup_le_normKernelSubgroup σ)

/-- Tate H⁻¹ vanishes for the actual cyclic idele module. -/
theorem herbrandHMinusOne_subsingleton (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    Subsingleton (HerbrandHMinusOne (L ≃ₐ[K] L) (IdeleGroup k L) σ) :=
  herbrandHMinusOne_subsingleton_of_normKernel_le_augmentationSubgroup σ
    (normKernel_le_augmentationSubgroup σ hσ)

variable [HasPrincipalDivisors k K]

/-- An actual norm-one idele in a cyclic extension is the quotient of a conjugate
idele by that idele. -/
theorem exists_div_of_norm_eq_one (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (a : IdeleGroup k L) (ha : norm (k := k) (K := K) (L := L) a = 1) :
    ∃ b : IdeleGroup k L, (σ • b) / b = a := by
  have ha' := (norm_eq_one_iff_tateNorm_eq_one (K := K) a).mp ha
  obtain ⟨b, hb⟩ := normKernel_le_augmentationSubgroup σ hσ ha'
  change σ • b * b⁻¹ = a at hb
  exact ⟨b, by simpa only [div_eq_mul_inv] using hb⟩

/-- The norm kernel equality also holds for the concrete completed norm homomorphism. -/
theorem norm_ker_eq_augmentationSubgroup (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    (norm (k := k) (K := K) (L := L)).ker =
      augmentationSubgroup (L ≃ₐ[K] L) (IdeleGroup k L) σ := by
  rw [norm_ker_eq_normKernelSubgroup, normKernel_eq_augmentationSubgroup σ hσ]

end FunctionField.IdeleGroup

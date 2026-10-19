/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Decomposition
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.LocalHilbert90
import Nyll.GaloisCohomology.Cyclic.MultiplicativeHilbert90

/-!
# Hilbert 90 for actual decomposition groups

The faithful completed action of the decomposition group satisfies Noether's
Hilbert 90. At ramification index one the local primitive can be corrected by a
base completion element to be an integral unit. These concrete statements give
the local field and unramified integral-unit vanishing needed for idele
cohomology; neither assumes a class-field axiom or a completed Galois comparison.
-/

noncomputable section

open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

open AlgebraicCurve
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

/-- Every multiplicative cocycle of the actual completed decomposition action
is the coboundary of an actual completed field unit. -/
theorem decomposition_isMulCoboundary_of_isMulCocycle (w : Place k L)
    (f : decompositionGroup (K := K) w → w.adicCompletionˣ)
    (hf : groupCohomology.IsMulCocycle₁ f) :
    groupCohomology.IsMulCoboundary₁ f :=
  groupCohomology.exists_unit_coboundary_of_injective_algAutHom
    (decompositionCompletionAut (K := K) w)
    (decompositionCompletionAut_injective (K := K) w) f hf

/-- At ramification index one, the same actual cocycle has an integral-unit primitive. -/
theorem exists_integral_decomposition_coboundary_of_ramificationIndex_eq_one
    (w : Place k L) (he : w.ramificationIndex K = 1)
    (f : decompositionGroup (K := K) w → w.adicCompletionˣ)
    (hf : groupCohomology.IsMulCocycle₁ f) :
    ∃ y : w.adicCompletionˣ, y ∈ w.adicCompletionIntegers.units ∧
      ∀ σ : decompositionGroup (K := K) w, (σ • y) / y = f σ := by
  obtain ⟨x, hx⟩ := decomposition_isMulCoboundary_of_isMulCocycle (K := K) w f hf
  obtain ⟨y, hy, hc⟩ :=
    exists_localUnit_coboundaries_of_ramificationIndex_eq_one (K := K) w he x
  exact ⟨y, hy, fun σ => (hc (decompositionCompletionAut (K := K) w σ)).trans (hx σ)⟩

/-- Integral units inherit the actual completed decomposition-group action. -/
instance decompositionLocalUnitsAction (w : Place k L) :
    MulDistribMulAction (decompositionGroup (K := K) w) w.adicCompletionIntegers.units where
  smul σ x := ⟨σ • (x : w.adicCompletionˣ),
    (decomposition_smul_mem_localUnits_iff (K := K) w σ x.1).mpr x.2⟩
  one_smul x := Subtype.ext (one_smul (decompositionGroup (K := K) w) x.1)
  mul_smul σ τ x := Subtype.ext (mul_smul σ τ x.1)
  smul_one σ := Subtype.ext (smul_one σ)
  smul_mul σ x y := Subtype.ext (smul_mul' σ x.1 y.1)

/-- Inclusion of integral units respects the actual decomposition action. -/
@[simp]
theorem coe_decomposition_localUnits_smul (w : Place k L)
    (σ : decompositionGroup (K := K) w) (x : w.adicCompletionIntegers.units) :
    ((σ • x : w.adicCompletionIntegers.units) : w.adicCompletionˣ) = σ • x.1 :=
  rfl

/-- The actual completed field-unit module has vanishing cyclic Tate norm obstruction. -/
theorem decomposition_normKernel_le_augmentationSubgroup (w : Place k L)
    (σ : decompositionGroup (K := K) w)
    (hσ : ∀ τ : decompositionGroup (K := K) w, τ ∈ Subgroup.zpowers σ) :
    normKernelSubgroup (decompositionGroup (K := K) w) w.adicCompletionˣ ≤
      augmentationSubgroup (decompositionGroup (K := K) w) w.adicCompletionˣ σ := by
  intro a ha
  obtain ⟨f, hf, hfa⟩ := CyclicCohomology.exists_mulCocycle_of_tateNorm_eq_one σ hσ a ha
  obtain ⟨y, hy⟩ := decomposition_isMulCoboundary_of_isMulCocycle (K := K) w f hf
  refine ⟨y, ?_⟩
  change σ • y * y⁻¹ = a
  simpa only [div_eq_mul_inv] using (hy σ).trans hfa

/-- Hilbert 90 for the actual cyclic decomposition-group field module. -/
theorem decomposition_herbrandHMinusOne_subsingleton (w : Place k L)
    (σ : decompositionGroup (K := K) w)
    (hσ : ∀ τ : decompositionGroup (K := K) w, τ ∈ Subgroup.zpowers σ) :
    Subsingleton (HerbrandHMinusOne (decompositionGroup (K := K) w) w.adicCompletionˣ σ) :=
  herbrandHMinusOne_subsingleton_of_normKernel_le_augmentationSubgroup σ
    (decomposition_normKernel_le_augmentationSubgroup (K := K) w σ hσ)

/-- Integral Hilbert 90 makes the actual local integral-unit norm kernel an augmentation
image at every place of ramification index one. -/
theorem decompositionLocalUnits_normKernel_le_augmentationSubgroup_of_ramificationIndex_eq_one
    (w : Place k L) (he : w.ramificationIndex K = 1)
    (σ : decompositionGroup (K := K) w)
    (hσ : ∀ τ : decompositionGroup (K := K) w, τ ∈ Subgroup.zpowers σ) :
    normKernelSubgroup (decompositionGroup (K := K) w) w.adicCompletionIntegers.units ≤
      augmentationSubgroup (decompositionGroup (K := K) w) w.adicCompletionIntegers.units σ := by
  intro a ha
  obtain ⟨f, hf, hfa⟩ := CyclicCohomology.exists_mulCocycle_of_tateNorm_eq_one σ hσ a ha
  have hf' : groupCohomology.IsMulCocycle₁
      (fun g : decompositionGroup (K := K) w => (f g : w.adicCompletionˣ)) := by
    intro g h
    exact congrArg Subtype.val (hf g h)
  obtain ⟨y, hy, hdiv⟩ := exists_integral_decomposition_coboundary_of_ramificationIndex_eq_one
    (K := K) w he (fun g => (f g : w.adicCompletionˣ)) hf'
  refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
  change σ • y * y⁻¹ = (a : w.adicCompletionˣ)
  simpa only [div_eq_mul_inv] using (hdiv σ).trans (congrArg Subtype.val hfa)

/-- The actual unramified local integral-unit module has vanishing cyclic Tate H⁻¹. -/
theorem decompositionLocalUnits_herbrandHMinusOne_subsingleton_of_ramificationIndex_eq_one
    (w : Place k L) (he : w.ramificationIndex K = 1)
    (σ : decompositionGroup (K := K) w)
    (hσ : ∀ τ : decompositionGroup (K := K) w, τ ∈ Subgroup.zpowers σ) :
    Subsingleton
      (HerbrandHMinusOne (decompositionGroup (K := K) w) w.adicCompletionIntegers.units σ) :=
  herbrandHMinusOne_subsingleton_of_normKernel_le_augmentationSubgroup σ
    (decompositionLocalUnits_normKernel_le_augmentationSubgroup_of_ramificationIndex_eq_one
      (K := K) w he σ hσ)

end FunctionField.IdeleGroup

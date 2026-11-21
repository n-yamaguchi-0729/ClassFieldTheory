/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionComparison
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.ChosenLocalization
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.LocalField
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.RestrictionDegree
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Tensor

/-! # The degree of the actual adic extension at every place above a finite place -/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField AlgebraicNumberTheory.Valuations HilbertRamification
open LocalClassFieldTheory LocalFieldTheory
open scoped NumberField ValuativeRel

namespace ClassFieldTheory.Brauer

universe u v

variable {K : Type u} [Field K] [NumberField K]

/-- All actual adic extensions over a finite place have the degree of the chosen completed stage. -/
theorem finitePlaceAdicCompletionMap_finrank_eq_chosen
    {L : Type v} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = v}) :
    let : Algebra (v.adicCompletion K) (W.1.adicCompletion L) :=
      (finitePlaceAdicCompletionMap K L v W).toAlgebra
    Module.finrank (v.adicCompletion K) (W.1.adicCompletion L) =
      Module.finrank (ChosenFinitePlaceBaseCompletion (K := K) v)
        (ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v) := by
  let vK := HeightOneSpectrum.adicAbv K v
  let w₀ := chosenFinitePlaceExtension (L := L) v
  let hvK := RayClass.adicAbv_isNontrivial v
  obtain ⟨a, rfl⟩ := (finitePlaceExtensionEquivAbove (K := K) (L := L) v).surjective W
  obtain ⟨σ, hσ⟩ := absoluteValueConjugacy vK hvK w₀ a
  subst a
  let a := absoluteValueExtensionConjugate vK w₀ σ
  let B := v.adicCompletion K
  let C := (finitePlaceExtensionEquivAbove (K := K) (L := L) v a).1.adicCompletion L
  let D := a.1.Completion
  let M := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v
  let : Algebra vK.Completion D := AbsoluteValue.completionAlgebra vK a.1 a.2
  let : Algebra B C := (finitePlaceAdicCompletionMap K L v
    (finitePlaceExtensionEquivAbove (K := K) (L := L) v a)).toAlgebra
  let eB : vK.Completion ≃+* B := (finitePlaceCompletionAlgEquiv v).toRingEquiv
  let eC : D ≃+* C := finitePlaceExtensionAdicCompletionRingEquiv (K := K) (L := L) v a
  have hcomp : (algebraMap B C).comp eB.toRingHom =
      eC.toRingHom.comp (algebraMap vK.Completion D) := by
    apply RingHom.ext
    intro x
    change finitePlaceAdicCompletionMap K L v (finitePlaceExtensionEquivAbove (K := K) (L := L) v a)
      (eB x) = eC (AbsoluteValue.completionMap vK a.1 a.2 x)
    rw [← finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap K L v a]
    change eC (AbsoluteValue.completionMap vK a.1 a.2 (eB.symm (eB x))) = _
    rw [eB.symm_apply_apply]
  let e₁ : D ≃ₐ[vK.Completion] w₀.1.Completion :=
    { __ := conjugateExtensionCompletionRingEquiv vK w₀ σ
      commutes' := conjugateExtensionCompletionRingEquiv_algebraMap vK w₀ σ }
  let e₂ : M ≃ₐ[vK.Completion] w₀.1.Completion := localizedCompletionEquivCompletion vK hvK w₀
  exact (Algebra.finrank_eq_of_equiv_equiv (R₀ := vK.Completion) (S₀ := D)
    (R₁ := B) (S₁ := C) eB eC hcomp).symm.trans
    ((e₁.trans e₂.symm).toLinearEquiv.finrank_eq)

/-- Divisibility by the chosen completed degree kills the original class at every place above it. -/
theorem finitePlaceBrauerRestriction_eq_zero_of_order_dvd_chosenDegree
    {L : Type u} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (W : {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = v})
    (x : Br (v.adicCompletion K))
    (h : addOrderOf x ∣ Module.finrank (ChosenFinitePlaceBaseCompletion (K := K) v)
      (ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v)) :
    restrict (finitePlaceAdicCompletionMap K L v W) x = 0 := by
  let B := v.adicCompletion K
  let C := W.1.adicCompletion L
  let : Algebra B C := (finitePlaceAdicCompletionMap K L v W).toAlgebra
  let : FiniteDimensional B C := finitePlaceAdicCompletionMap_moduleFinite K L v W
  let : CharZero B := charZero_of_injective_algebraMap (algebraMap K B).injective
  let : Algebra.IsIntegral B C := Algebra.IsIntegral.of_finite _ _
  let : Algebra.IsSeparable B C := Algebra.IsSeparable.of_integral _ _
  let : ValuativeRel B := ClassFieldTheory.finitePlaceCompletionValuativeRel K v
  let : IsNonarchimedeanLocalField B :=
    ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField K v
  change restrict (algebraMap B C) x = 0
  apply (restrict_eq_zero_iff_finrank_nsmul_localBrauerInvariant B C x).mpr
  rw [finitePlaceAdicCompletionMap_finrank_eq_chosen v W, ← map_nsmul,
    (addOrderOf_dvd_iff_nsmul_eq_zero.mp h), map_zero]

end ClassFieldTheory.Brauer

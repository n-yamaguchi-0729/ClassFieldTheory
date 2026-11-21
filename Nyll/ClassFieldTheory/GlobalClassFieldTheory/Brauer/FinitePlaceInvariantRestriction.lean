/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.FiniteCompletionDegree
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.InvariantSum
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.NormRestriction
public import Nyll.ValuedFieldTheory.Valuation.Completion.DegreeNormTrace

/-! # Summing the actual local degrees and restricting arithmetic invariants -/

@[expose] public section

open AlgebraicNumberTheory.Valuations GlobalClassFieldTheory.Reciprocity
open IsDedekindDomain LocalFieldTheory NumberField
open scoped BigOperators NumberField ValuativeRel

noncomputable section
namespace ClassFieldTheory.Brauer

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

local notation "Above[" v "]" => {W : HeightOneSpectrum (𝓞 L) // finitePlaceBelow (K := K) W = v}

/-- The degree of the actual adic completion map at the specified place above `v`. -/
def adicCompletionDegree (v : HeightOneSpectrum (𝓞 K)) (W : Above[v]) : ℕ :=
  let : Algebra (v.adicCompletion K) (W.val.adicCompletion L) :=
    (finitePlaceAdicCompletionMap K L v W).toAlgebra
  Module.finrank (v.adicCompletion K) (W.val.adicCompletion L)

variable [FiniteDimensional K L]

/-- Enumeration of the finite restriction fiber by the actual extensions of the absolute value. -/
abbrev finitePlaceRestrictionFiberFintype (v : HeightOneSpectrum (𝓞 K)) : Fintype (Above[v]) :=
  let _ := completionTensorDecomposition_extensionFintype (K := K) (L := L)
    (HeightOneSpectrum.adicAbv K v) (RayClass.adicAbv_isNontrivial v)
  Fintype.ofEquiv _ (finitePlaceExtensionEquivAbove (K := K) (L := L) v)

private theorem adicCompletionDegree_eq_extension (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv K v) L) :
    let : Algebra (HeightOneSpectrum.adicAbv K v).Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra (HeightOneSpectrum.adicAbv K v) w.1 w.2
    adicCompletionDegree v (finitePlaceExtensionEquivAbove (K := K) (L := L) v w) =
      Module.finrank (HeightOneSpectrum.adicAbv K v).Completion w.1.Completion := by
  intro localAlgebra
  let vK := HeightOneSpectrum.adicAbv K v
  let A := vK.Completion
  let B := w.1.Completion
  let C := v.adicCompletion K
  let W := finitePlaceExtensionEquivAbove (K := K) (L := L) v w
  let D := W.val.adicCompletion L
  let a : C →+* D := finitePlaceAdicCompletionMap K L v W
  let : Algebra C D := a.toAlgebra
  let e₁ : A ≃+* C := (finitePlaceCompletionAlgEquiv v).toRingEquiv
  let e₂ : B ≃+* D := finitePlaceExtensionAdicCompletionRingEquiv (K := K) (L := L) v w
  have hcomp : (algebraMap C D).comp e₁.toRingHom =
      e₂.toRingHom.comp (algebraMap A B) := by
    apply RingHom.ext
    intro x
    change a (e₁ x) = e₂ (AbsoluteValue.completionMap vK w.1 w.2 x)
    change finitePlaceAdicCompletionMap K L v W (e₁ x) = _
    rw [← finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap K L v w]
    change e₂ (AbsoluteValue.completionMap vK w.1 w.2 (e₁.symm (e₁ x))) = _
    rw [e₁.symm_apply_apply]
  exact (Algebra.finrank_eq_of_equiv_equiv (R₀ := A) (S₀ := B)
    (R₁ := C) (S₁ := D) e₁ e₂ hcomp).symm

/-- The completed degrees over one finite place sum to the original number-field degree. -/
theorem sum_adicCompletionDegree (v : HeightOneSpectrum (𝓞 K)) :
    let _ := finitePlaceRestrictionFiberFintype (L := L) v
    (∑ W : Above[v], adicCompletionDegree v W) = Module.finrank K L := by
  intro finiteOwner
  let vK := HeightOneSpectrum.adicAbv K v
  let hvK := RayClass.adicAbv_isNontrivial v
  let _ := completionTensorDecomposition_extensionFintype (K := K) (L := L) vK hvK
  let : ∀ w : AbsoluteValueExtension vK L, Algebra vK.Completion w.1.Completion :=
    fun w => AbsoluteValue.completionAlgebra vK w.1 w.2
  let e := finitePlaceExtensionEquivAbove (K := K) (L := L) v
  change (∑ W : Above[v], adicCompletionDegree v W) = _
  calc
    _ = ∑ w : AbsoluteValueExtension vK L, Module.finrank vK.Completion w.1.Completion := by
      symm
      apply Fintype.sum_equiv e
      intro w
      exact (adicCompletionDegree_eq_extension v w).symm
    _ = _ := (completionDegreeNormTrace_degree (K := K) (L := L) vK hvK).symm

private theorem restrictionInvariant_via_completionEquivs
    {F M A B : Type} [Field F] [Field M] [Field A] [Field B]
    [Algebra F M] [CharZero F] [Algebra A B] [FiniteDimensional A B]
    [ValuativeRel F] [ValuativeRel M]
    [TopologicalSpace F] [TopologicalSpace M]
    [IsNonarchimedeanLocalField F] [IsNonarchimedeanLocalField M]
    [Valuation.HasExtension (ValuativeRel.valuation F) (ValuativeRel.valuation M)]
    (eF : F ≃+* A) (eM : M ≃+* B)
    (hcomp : (algebraMap A B).comp eF.toRingHom = eM.toRingHom.comp (algebraMap F M))
    (x : Br A) :
    localBrauerInvariant M (restrict eM.symm.toRingHom (restrict (algebraMap A B) x)) =
      Module.finrank A B • localBrauerInvariant F (restrict eF.symm.toRingHom x) := by
  have hdegree := Algebra.finrank_eq_of_equiv_equiv (R₀ := F) (S₀ := M)
    (R₁ := A) (S₁ := B) eF eM hcomp
  have hpos : 0 < Module.finrank A B := Module.finrank_pos
  let : FiniteDimensional F M := Module.finite_of_finrank_pos (hdegree.symm ▸ hpos)
  let : Algebra.IsIntegral F M := Algebra.IsIntegral.of_finite F M
  let : Algebra.IsSeparable F M := Algebra.IsSeparable.of_integral F M
  have hmaps : eM.symm.toRingHom.comp (algebraMap A B) =
      (algebraMap F M).comp eF.symm.toRingHom := by
    apply RingHom.ext
    intro y
    let z := eF.symm y
    have h := DFunLike.congr_fun hcomp z
    change algebraMap A B (eF (eF.symm y)) = eM (algebraMap F M (eF.symm y)) at h
    rw [eF.apply_symm_apply] at h
    exact (congrArg eM.symm h).trans (eM.symm_apply_apply _)
  have hrestrict :
      restrict eM.symm.toRingHom (restrict (algebraMap A B) x) =
        restrict (algebraMap F M) (restrict eF.symm.toRingHom x) := by
    change ((restrict eM.symm.toRingHom).comp (restrict (algebraMap A B))) x =
      ((restrict (algebraMap F M)).comp (restrict eF.symm.toRingHom)) x
    rw [restrict_comp, restrict_comp, hmaps]
  rw [hrestrict, localBrauerInvariant_restrict F M, hdegree]

/-- Restriction of an actual finite-place class multiplies its canonical
invariant by the local degree. -/
theorem finitePlaceBrauerInvariant_restrict (v : HeightOneSpectrum (𝓞 K))
    (W : Above[v]) (x : Br (v.adicCompletion K)) :
    finitePlaceBrauerInvariantEquiv L W.val (restrict (finitePlaceAdicCompletionMap K L v W) x) =
      adicCompletionDegree v W • finitePlaceBrauerInvariantEquiv K v x := by
  let F := (HeightOneSpectrum.adicAbv K v).Completion
  let M := (HeightOneSpectrum.adicAbv L W.val).Completion
  let A := v.adicCompletion K
  let B := W.val.adicCompletion L
  let a : A →+* B := finitePlaceAdicCompletionMap K L v W
  let eF : F ≃+* A := (finitePlaceCompletionAlgEquiv v).toRingEquiv
  let eM : M ≃+* B := (finitePlaceCompletionAlgEquiv W.val).toRingEquiv
  let f : F →+* M := finitePlaceArtinRelativeCompletionRingHom v W.val W.property
  let : Algebra A B := a.toAlgebra
  let : Algebra F M := f.toAlgebra
  let : ValuativeRel F := finitePlaceLocalArtinCompletionValuativeRel v
  let : ValuativeRel M := finitePlaceLocalArtinCompletionValuativeRel W.val
  let : IsNonarchimedeanLocalField F := finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let : IsNonarchimedeanLocalField M :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField W.val
  have hcomp : (algebraMap A B).comp eF.toRingHom = eM.toRingHom.comp (algebraMap F M) := by
    apply RingHom.ext
    intro y
    change a (eF y) = eM (eM.symm (a (eF y)))
    exact (eM.apply_symm_apply _).symm
  let : FiniteDimensional A B := finitePlaceAdicCompletionMap_moduleFinite K L v W
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let : (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation M) :=
    finitePlaceArtinCompletionHasExtension v W.val W.property
  let xA := restrict a x
  let xF := restrict eF.symm.toRingHom x
  let xM := restrict eM.symm.toRingHom xA
  have hLeft : finitePlaceBrauerInvariantEquiv L W.val xA =
      finitePlaceNormalizedBrauerInvariantEquiv L W.val xM :=
    finitePlaceBrauerInvariantEquiv_apply L W.val xA
  have hRight : finitePlaceBrauerInvariantEquiv K v x =
      finitePlaceNormalizedBrauerInvariantEquiv K v xF :=
    finitePlaceBrauerInvariantEquiv_apply K v x
  have hLocal : localBrauerInvariant M xM = Module.finrank A B • localBrauerInvariant F xF :=
    restrictionInvariant_via_completionEquivs (F := F) (M := M) (A := A) (B := B) eF eM hcomp x
  have hNormalized : finitePlaceNormalizedBrauerInvariantEquiv L W.val xM =
      Module.finrank A B • finitePlaceNormalizedBrauerInvariantEquiv K v xF := hLocal
  change finitePlaceBrauerInvariantEquiv L W.val xA =
    Module.finrank A B • finitePlaceBrauerInvariantEquiv K v x
  exact hLeft.trans (hNormalized.trans (congrArg (Module.finrank A B • ·) hRight.symm))

end ClassFieldTheory.Brauer

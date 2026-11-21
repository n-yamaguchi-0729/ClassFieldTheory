/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.CyclicRestriction
public import Nyll.ClassFieldTheory.Algebra.Brauer.EmbeddedInflation
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.InfinitePlaceModel
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.LocalBlocks
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.Localization
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Algebra

/-! # Infinite-place Brauer restriction at the actual completed stage -/

@[expose] public section

noncomputable section

open AlgebraicNumberTheory.Valuations ClassFieldTower.Cohomology HilbertRamification
open LocalClassFieldTheory LocalFieldTheory NumberField
open scoped NumberField

namespace ClassFieldTheory.Brauer

universe u

private theorem embeddedRelativeRestriction_cyclicClass_eq_zero_iff_norm
    {K F M : Type u} [Field K] [Field F] [Field M]
    [Algebra K F] [Algebra F M] [Algebra K M] [IsScalarTower K F M]
    [FiniteDimensional F M] [IsGalois F M]
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) [IsCyclic Gal(E/K)]
    (g : Gal(E/K)) (hg : ∀ σ : Gal(E/K), σ ∈ Subgroup.zpowers g)
    (j : E →ₐ[K] M) (hj : Function.Injective (embeddedGaloisRestriction (B := F) j))
    (a : Kˣ) :
    embeddedRelativeRestriction (A := F) E j
        (cyclicContinuousUnitClass K E g hg (Additive.ofMul a)) = 0 ↔
      Units.map (algebraMap K F).toMonoidHom a ∈ localNormSubgroup F M := by
  let r := (embeddedGaloisRestriction (B := F) j).toMonoidHom
  let : CommGroup Gal(E/K) := IsCyclic.commGroup
  let : IsCyclic Gal(M/F) := isCyclic_of_injective r hj
  obtain ⟨h, hh, hgen, hcard⟩ := finiteCyclic_exists_generator_map_index g hg r hj
  have hd := Nat.pos_of_ne_zero r.range.index_ne_zero_of_finite
  let aF := Units.map (algebraMap K F).toMonoidHom a
  let e := (continuousRelativeUnitsH2Equiv F M).symm
  have hclass : cyclicContinuousUnitClass F M h hh (Additive.ofMul aF) = 0 ↔
      aF ∈ localNormSubgroup F M := by
    change e (cyclicUnitClass F M h hh (Additive.ofMul aF)) = 0 ↔ _
    exact (Iff.intro
      (fun hz => e.injective (hz.trans (map_zero e).symm))
      (fun hz => (congrArg e hz).trans (map_zero e))).trans
      (cyclicUnitClass_eq_zero_iff_norm F M h hh aF)
  rw [embeddedRelativeRestriction_cyclicContinuousUnitClass (F := F) E j g hg h hh
    r.range.index hd hcard hgen a]
  exact hclass

private theorem embeddedGaloisRestriction_localizedCompletion_injective
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) (w : AbsoluteValueExtension vK L) :
    let : Algebra vK.Completion (LocalizedCompletion vK w) :=
      localizedCompletionBaseAlgebra vK w
    let : Algebra K (LocalizedCompletion vK w) := localizedCompletionGlobalAlgebra vK w
    let : IsScalarTower K vK.Completion (LocalizedCompletion vK w) :=
      localizedCompletionIsScalarTower vK w
    Function.Injective (embeddedGaloisRestriction (B := vK.Completion)
      (localizedCompletionToAlgHom vK w)) := by
  intro baseAlgebra globalAlgebra scalarTower
  let F := vK.Completion
  let M := LocalizedCompletion vK w
  let D := absoluteValueDecompositionGroup K w.1
  let j : L →ₐ[K] M := localizedCompletionToAlgHom vK w
  let r : Gal(M/F) →ₜ* Gal(L/K) := embeddedGaloisRestriction (B := F) j
  let e : D ≃* Gal(M/F) := decompositionGroupEquivAlgebraicLocalizationAut vK hvK w
  have hr (σ : D) : r (e σ) = σ.val := by
    apply AlgEquiv.ext
    intro x
    apply j.injective
    calc
      j (r (e σ) x) = e σ (j x) := embeddedGaloisRestriction_commutes (B := F) j (e σ) x
      _ = j (σ.val x) :=
        localizationRamificationGroups_decompositionGroupEquiv_toLocalization vK hvK w σ x
  have hcomp : Function.Injective (r ∘ e) := by
    intro σ τ h
    exact Subtype.val_injective ((hr σ).symm.trans (h.trans (hr τ)))
  exact hcomp.of_comp_right e.surjective

private theorem localizedCompletion_cyclicClass_eq_zero_iff_norm
    {K : Type u} [Field K] (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    [IsCyclic Gal(E/K)] (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK E)
    (g : Gal(E/K)) (hg : ∀ σ : Gal(E/K), σ ∈ Subgroup.zpowers g) (a : Kˣ) :
    let : Algebra vK.Completion (LocalizedCompletion vK w) := localizedCompletionBaseAlgebra vK w
    let : Algebra K (LocalizedCompletion vK w) := localizedCompletionGlobalAlgebra vK w
    let : IsScalarTower K vK.Completion (LocalizedCompletion vK w) :=
      localizedCompletionIsScalarTower vK w
    let : IsGalois vK.Completion (LocalizedCompletion vK w) := localizedCompletionIsGalois vK w
    embeddedRelativeRestriction (A := vK.Completion) E (localizedCompletionToAlgHom vK w)
        (cyclicContinuousUnitClass K E g hg (Additive.ofMul a)) = 0 ↔
      Units.map (algebraMap K vK.Completion).toMonoidHom a ∈
        localNormSubgroup vK.Completion (LocalizedCompletion vK w) := by
  intro baseAlgebra globalAlgebra tower galois
  let F := vK.Completion
  let M := LocalizedCompletion vK w
  let : FiniteDimensional F M := localizedCompletionFiniteDimensional vK hvK w
  let j : E →ₐ[K] M := localizedCompletionToAlgHom vK w
  have hj : Function.Injective (embeddedGaloisRestriction (B := F) j) :=
    embeddedGaloisRestriction_localizedCompletion_injective vK hvK w
  exact embeddedRelativeRestriction_cyclicClass_eq_zero_iff_norm
    (F := F) (M := M) E g hg j hj a

variable {K : Type u} [Field K] [NumberField K]
    (v : InfinitePlace K) (E : FiniteGaloisIntermediateField K (SeparableClosure K)) [NumberField E]

/-- The chosen extension of the actual infinite absolute value to the original finite stage. -/
abbrev chosenInfinitePlaceExtension : AbsoluteValueExtension v.1 E :=
  infinitePlaceAbsoluteValueExtension v (chosenInfinitePlaceAbove (L := E) v)
    (chosenInfinitePlaceAbove_comap (L := E) v)

/-- Norm subgroup of the actual localized completion for a specified absolute-value extension. -/
def localizedCompletionNormSubgroup {K L : Type u} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (w : AbsoluteValueExtension vK L) : Subgroup vK.Completionˣ := by
  let := localizedCompletionBaseAlgebra vK w
  exact localNormSubgroup vK.Completion (LocalizedCompletion vK w)

omit [NumberField K] [NumberField ↥E.toIntermediateField] in
/-- Localization of the actual global cyclic class vanishes exactly on norms
from the completion at the specified extension of the infinite place. -/
theorem infinitePlaceRestriction_cyclicBrauerClass_eq_zero_iff_localizedNorm
    [IsCyclic Gal(E/K)] (w : AbsoluteValueExtension v.1 E)
    (g : Gal(E/K)) (hg : ∀ σ : Gal(E/K), σ ∈ Subgroup.zpowers g) (a : Kˣ) :
    infinitePlaceRestriction K v (cyclicBrauerClass E g hg a) = 0 ↔
      Units.map (algebraMap K v.1.Completion).toMonoidHom a ∈
        localizedCompletionNormSubgroup v.1 w := by
  let F := v.1.Completion
  let M := LocalizedCompletion v.1 w
  let : Algebra F M := localizedCompletionBaseAlgebra v.1 w
  let : Algebra K M := localizedCompletionGlobalAlgebra v.1 w
  let : IsScalarTower K F M := localizedCompletionIsScalarTower v.1 w
  let : IsGalois F M := localizedCompletionIsGalois v.1 w
  let : FiniteDimensional F M := localizedCompletionFiniteDimensional v.1 v.isNontrivial w
  let e : F ≃ₐ[K] v.Completion := (infinitePlaceCompletionAlgEquiv v).symm
  let j : E →ₐ[K] M := localizedCompletionToAlgHom v.1 w
  let x : relativeBr E := cyclicContinuousUnitClass K E g hg (Additive.ofMul a)
  let R : relativeBr E →+ continuousCohomology 2 (galoisUnitsRep F M) :=
    embeddedRelativeRestriction (A := F) E j
  have hLoc : infinitePlaceRestriction K v (cyclicBrauerClass E g hg a) = 0 ↔ R x = 0 :=
    restrict_finiteInflation_eq_zero_iff_embeddedRelativeRestriction
      (A := F) (B := v.Completion) (M := M) E e j x
  have hNorm : R x = 0 ↔ Units.map (algebraMap K F).toMonoidHom a ∈
      localizedCompletionNormSubgroup v.1 w :=
    localizedCompletion_cyclicClass_eq_zero_iff_norm E v.1 v.isNontrivial w g hg a
  exact hLoc.trans hNorm

end ClassFieldTheory.Brauer

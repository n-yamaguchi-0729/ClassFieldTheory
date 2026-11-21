/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.CyclicNorm
public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteRestrictionKernel
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.ComplexPlace
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.FiniteCompletionDegree
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.LocalizationInjective
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.LocalizationNaturality
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.SimultaneousCyclicSplitting

/-! # Cyclic carry representatives and their actual splitting fields -/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField
open scoped DirectSum NumberField

namespace ClassFieldTheory.Brauer

universe u

section CyclicClass

variable {K : Type u} [Field K]
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) [IsCyclic Gal(E/K)]
    (g : Gal(E/K)) (hg : ∀ σ : Gal(E/K), σ ∈ Subgroup.zpowers g)

/-- A class split by a given finite cyclic extension is an actual carry class of a base unit. -/
theorem exists_cyclicBrauerClass_eq (x : Br K) (hx : restrict (algebraMap K E) x = 0) :
    ∃ a : Kˣ, cyclicBrauerClass E g hg a = x := by
  obtain ⟨y, rfl⟩ := exists_finiteInflation_of_restrict_eq_zero E x hx
  obtain ⟨a, ha⟩ := cyclicUnitClass_surjective K E g hg (continuousRelativeUnitsH2Equiv K E y)
  refine ⟨a.toMul, ?_⟩
  change finiteInflation E ((continuousRelativeUnitsH2Equiv K E).symm
    (cyclicUnitClass K E g hg a)) = finiteInflation E y
  rw [ha, AddEquiv.symm_apply_apply]

end CyclicClass

variable {K : Type u} [Field K] [NumberField K]

/-- A finite extension that kills the actual localized classes at every
place above a place of the base kills the original global class. -/
theorem restrict_eq_zero_of_localCompletionRestrictions
    (E : Type u) [Field E] [NumberField E] [Algebra K E] (x : Br K)
    (hf : ∀ w : HeightOneSpectrum (𝓞 E),
      let v := finitePlaceBelow (K := K) w
      restrict (finitePlaceAdicCompletionMap K E v ⟨w, rfl⟩) (finitePlaceRestriction K v x) = 0)
    (hi : ∀ w : InfinitePlace E,
      let v := w.comap (algebraMap K E)
      restrict (infinitePlaceBrauerCompletionMap v w rfl) (infinitePlaceRestriction K v x) = 0) :
    restrict (algebraMap K E) x = 0 := by
  apply localization_injective (K := E)
  rw [map_zero]
  apply DirectSum.ext
  intro w
  rw [localization_apply, DirectSum.zero_apply]
  cases w with
  | inl w =>
    let v := finitePlaceBelow (K := K) w
    have h := DFunLike.congr_fun (finitePlaceRestriction_comp_restrict v ⟨w, rfl⟩) x
    exact h.trans (hf w)
  | inr w =>
    let v := w.comap (algebraMap K E)
    have h := DFunLike.congr_fun (infinitePlaceRestriction_comp_restrict v w rfl) x
    exact h.trans (hi w)

/-- The chosen finite local degree divisibilities and the ramification at real
places ensure that the original global class splits over the given finite field. -/
theorem restrict_eq_zero_of_localOrders
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) [NumberField E] (x : Br K)
    (hf : ∀ v : HeightOneSpectrum (𝓞 K), addOrderOf (finitePlaceRestriction K v x) ∣
      Module.finrank (ChosenFinitePlaceBaseCompletion (K := K) v)
        (ChosenFinitePlaceLocalizedCompletion (K := K) (L := E) v))
    (hi : ∀ v : InfinitePlace K, v.IsReal → (chosenInfinitePlaceAbove (L := E) v).IsRamified K) :
    restrict (algebraMap K E) x = 0 := by
  apply restrict_eq_zero_of_localCompletionRestrictions E x
  · intro w
    let v := finitePlaceBelow (K := K) w
    exact finitePlaceBrauerRestriction_eq_zero_of_order_dvd_chosenDegree v ⟨w, rfl⟩
      (finitePlaceRestriction K v x) (hf v)
  · intro w
    let v := w.comap (algebraMap K E)
    by_cases hv : v.IsReal
    · let w₀ := chosenInfinitePlaceAbove (L := E) v
      obtain ⟨σ, hσ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq
        (chosenInfinitePlaceAbove_comap (L := E) v : w₀.comap (algebraMap K E) =
          w.comap (algebraMap K E))
      have hw : w.IsComplex := by
        rw [← InfinitePlace.not_isReal_iff_isComplex, ← hσ, InfinitePlace.isReal_smul_iff]
        exact InfinitePlace.not_isReal_iff_isComplex.mpr (hi v hv).isComplex
      let : Subsingleton (Br w.Completion) := complexPlace_br_subsingleton hw
      exact Subsingleton.elim _ _
    · change restrict (infinitePlaceBrauerCompletionMap v w rfl)
        (infinitePlaceRestriction K v x) = 0
      rw [DFunLike.congr_fun (infinitePlaceRestriction_eq_zero_of_isComplex
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)) x, AddMonoidHom.zero_apply, map_zero]

/-- Every global cohomological Brauer class is represented by a carry in an
actual finite cyclic extension. -/
theorem exists_cyclicBrauerRepresentative (x : Br K) :
    ∃ E : FiniteGaloisIntermediateField K (SeparableClosure K), ∃ hcyc : IsCyclic Gal(E/K),
      let : IsCyclic Gal(E/K) := hcyc
      ∃ (g : Gal(E/K)) (hg : ∀ σ : Gal(E/K), σ ∈ Subgroup.zpowers g) (a : Kˣ),
        cyclicBrauerClass E g hg a = x := by
  obtain ⟨E, hcyc, hfin, hinf⟩ := exists_cyclicStage_for_localBrauerTuple K (localization K x)
  let : NumberField E := NumberField.of_module_finite K E
  let : IsCyclic Gal(E/K) := hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(E/K))
  have hfin' (v : HeightOneSpectrum (𝓞 K)) :
      addOrderOf (finitePlaceRestriction K v x) ∣
        Module.finrank (ChosenFinitePlaceBaseCompletion (K := K) v)
          (ChosenFinitePlaceLocalizedCompletion (K := K) (L := E) v) := by
    have h := hfin v
    rw [localization_apply] at h
    exact h
  have hvan := restrict_eq_zero_of_localOrders E x hfin' hinf
  obtain ⟨a, ha⟩ := exists_cyclicBrauerClass_eq E g hg x hvan
  exact ⟨E, hcyc, g, hg, a, ha⟩

end ClassFieldTheory.Brauer

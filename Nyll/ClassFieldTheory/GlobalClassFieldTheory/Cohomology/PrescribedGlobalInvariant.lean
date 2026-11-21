/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.SimultaneousCyclicSplitting
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.LocalizedCompletionRefinement
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.SupportedIdeleInvariant

/-! # A prescribed arithmetic invariant at a finite global stage -/

@[expose] public section

open AlgebraicNumberTheory.Valuations ClassFieldTheory.Brauer IsDedekindDomain NumberField
open scoped DirectSum NumberField

namespace GlobalClassFieldTheory.Cohomology

variable (K : Type) [Field K] [NumberField K]

open scoped Classical in
private theorem exists_supportedPrescribedInvariantOnStage
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) [NumberField E]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+) (z : AddCircle (1 : ℚ))
    (hz : (n : ℕ) • z = 0)
    (hd : (n : ℕ) ∣ Module.finrank (ChosenFinitePlaceBaseCompletion (K := K) v)
      (ChosenFinitePlaceLocalizedCompletion (K := K) (L := E) v)) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K)))
      (hfin : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S →
        ChosenFinitePlaceIsUnramified (K := K) (L := E) w)
      (x : SupportedLocalH2 K E S),
      (∃ b : Br (v.adicCompletion K), supportedBrauerTuple K E S x =
          DirectSum.of (fun p : Place K => Br (placeCompletion K p)) (Sum.inl v) b ∧
        finitePlaceBrauerInvariantEquiv K v b = z) ∧
      supportedBrauerInvariantSum K E S x = z ∧
        (prescribedSupportedIdeleClassH2 K E S hfin x = 0 → z = 0) := by
  classical
  let S₀ := ideleClassHerbrandSupport (K := K) (L := E)
  let S := insert v S₀
  have hsub : S₀ ⊆ S := fun _ hw => Finset.mem_insert_of_mem hw
  let hfin (w : HeightOneSpectrum (𝓞 K)) (hw : w ∉ S) :=
    chosenFinitePlaceIsUnramified_of_notMem_ideleClassHerbrandSupport
      (K := K) (L := E) w (fun h => hw (hsub h))
  have hlocal : finiteTensorCompletedDegree E v • z = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mp
      ((addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz).trans hd)
  obtain ⟨x, b, ht, hb⟩ := exists_supportedBrauerTuple_single_of_nsmul_eq_zero K E S v
    (Finset.mem_insert_self _ _) z hlocal
  have hx : supportedBrauerInvariantSum K E S x = z :=
    (supportedBrauerInvariantSum_eq_of_tuple_single K E S v x b ht).trans hb
  refine ⟨S, hfin, x, ⟨b, ht, hb⟩, hx, ?_⟩
  intro h
  have hk := prescribedSupportedIdeleClassH2_ker_le_invariantSum_ker K E S hfin h
  exact hx.symm.trans hk

open scoped Classical in
/-- Any invariant of given positive denominator is realized at a specified
finite place in an actual finite cyclic stage. Its supported idèle class
has nonzero image in the standard class cohomology when the invariant is nonzero. -/
theorem exists_onePlacePrescribedGlobalInvariant
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+) (z : AddCircle (1 : ℚ))
    (hz : (n : ℕ) • z = 0) :
    ∃ E : FiniteGaloisIntermediateField K (SeparableClosure K), IsCyclic Gal(E/K) ∧
      let _ : NumberField E := NumberField.of_module_finite K E
      ∃ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (hfin : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S →
          ChosenFinitePlaceIsUnramified (K := K) (L := E) w)
        (x : SupportedLocalH2 K E S),
        (∃ b : Br (v.adicCompletion K), supportedBrauerTuple K E S x =
            DirectSum.of (fun p : Place K => Br (placeCompletion K p)) (Sum.inl v) b ∧
          finitePlaceBrauerInvariantEquiv K v b = z) ∧
        supportedBrauerInvariantSum K E S x = z ∧
          (prescribedSupportedIdeleClassH2 K E S hfin x = 0 → z = 0) := by
  obtain ⟨E, hcyc, hd, _⟩ := exists_cyclicStage_finitePlace_degree_dvd_and_ramifies_real
    K (fun _ : Unit => v) (fun _ => n)
  let : NumberField E := NumberField.of_module_finite K E
  exact ⟨E, hcyc, exists_supportedPrescribedInvariantOnStage K E v n z hz (hd ())⟩

open scoped Classical in
/-- The one-place invariant can be realized on an actual refinement of any
given finite Galois stage. The refinement is formed in the original separable closure. -/
theorem exists_refinement_onePlacePrescribedGlobalInvariant
    (L : FiniteGaloisIntermediateField K (SeparableClosure K))
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+) (z : AddCircle (1 : ℚ))
    (hz : (n : ℕ) • z = 0) :
    ∃ E : FiniteGaloisIntermediateField K (SeparableClosure K), L ≤ E ∧
      let _ : NumberField E := NumberField.of_module_finite K E
      ∃ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (hfin : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S →
          ChosenFinitePlaceIsUnramified (K := K) (L := E) w)
        (x : SupportedLocalH2 K E S),
        (∃ b : Br (v.adicCompletion K), supportedBrauerTuple K E S x =
            DirectSum.of (fun p : Place K => Br (placeCompletion K p)) (Sum.inl v) b ∧
          finitePlaceBrauerInvariantEquiv K v b = z) ∧
        supportedBrauerInvariantSum K E S x = z ∧
          (prescribedSupportedIdeleClassH2 K E S hfin x = 0 → z = 0) := by
  obtain ⟨M, _, hd, _⟩ := exists_cyclicStage_finitePlace_degree_dvd_and_ramifies_real
    K (fun _ : Unit => v) (fun _ => n)
  let E := L ⊔ M
  let : NumberField M := NumberField.of_module_finite K M
  let : NumberField E := NumberField.of_module_finite K E
  let j : M →ₐ[K] E := IntermediateField.inclusion
    ((FiniteGaloisIntermediateField.le_iff M E).mp le_sup_right)
  have hlocal := localizedCompletion_finrank_dvd_of_embedding j (HeightOneSpectrum.adicAbv K v)
    (chosenFinitePlaceExtension (L := M) v) (chosenFinitePlaceExtension (L := E) v)
  exact ⟨E, le_sup_left,
    exists_supportedPrescribedInvariantOnStage K E v n z hz ((hd ()).trans hlocal)⟩

end GlobalClassFieldTheory.Cohomology

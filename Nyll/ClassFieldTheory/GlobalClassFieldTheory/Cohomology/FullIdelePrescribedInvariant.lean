/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.PrescribedGlobalInvariant

/-! # Realization of the prescribed tuple in the full idèle group -/

@[expose] public section

open CategoryTheory ClassFieldTheory.Brauer ClassFieldTower.Martinet.Shafarevich
open IsDedekindDomain NumberField
open scoped DirectSum NumberField

noncomputable section
namespace GlobalClassFieldTheory.Cohomology

variable (K : Type) [Field K] [NumberField K]

open scoped Classical in
/-- A finite Galois refinement contains a full idèle class whose literal
Brauer tuple is the specified class at one finite place. -/
theorem exists_refinement_fullIdele_onePlace
    (L : FiniteGaloisIntermediateField K (SeparableClosure K))
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ+) (z : AddCircle (1 : ℚ))
    (hz : (n : ℕ) • z = 0) :
    ∃ E : FiniteGaloisIntermediateField K (SeparableClosure K), L ≤ E ∧
      let _ : NumberField E := NumberField.of_module_finite K E
      ∃ (x : groupCohomology (finiteIdeleShortComplex K E).X₂ 2) (b : Br (v.adicCompletion K)),
        fullIdeleBrauerTuple K E x =
          DirectSum.of (fun p : Place K => Br (placeCompletion K p)) (Sum.inl v) b ∧
        finitePlaceBrauerInvariantEquiv K v b = z := by
  obtain ⟨E', hLE, S', hfin, x, ⟨b, hb, hvalue⟩, _, _⟩ :=
    exists_refinement_onePlacePrescribedGlobalInvariant K L v n z hz
  let : NumberField E' := NumberField.of_module_finite K E'
  exact ⟨E', hLE, supportedFullIdeleH2 K E' S' hfin x, b,
    (fullIdeleBrauerTuple_supportedFullIdeleH2 K E' S' hfin x).trans hb, hvalue⟩

end GlobalClassFieldTheory.Cohomology

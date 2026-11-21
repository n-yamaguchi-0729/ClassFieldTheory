/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteRepresentative
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.FiniteBadPlaces

/-!
# Finite support of the arithmetic data of a Brauer representative

Each class has an actual finite-stage cocycle whose coefficient units and
extension are simultaneously good at every place above one finite set.
-/

@[expose] public section

noncomputable section

universe u

open IsDedekindDomain NumberField
open scoped NumberField

namespace ClassFieldTheory.Brauer

variable {K : Type u} [Field K] [NumberField K]

omit [NumberField K] in
/-- The actual field unit obtained by evaluating a relative homogeneous cocycle. -/
def relativeCocycleValue (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (z : ContinuousCohomology.cocycles (galoisUnitsRep K E) 2)
    (a : Gal(E/K) × Gal(E/K) × Gal(E/K)) : Eˣ :=
  (show Additive Eˣ from
    ((TopRep.homogeneousCochains (galoisUnitsRep K E)).iCycles 2 z).val a.1 a.2.1 a.2.2).toMul

/-- At almost every finite place a single representative of the given class
has unramified splitting field and unit coefficients at every place above it. -/
theorem exists_finiteInflation_unit_support (x : Br K) :
    ∃ (E : FiniteGaloisIntermediateField K (SeparableClosure K))
      (z : ContinuousCohomology.cocycles (galoisUnitsRep K E) 2),
      finiteInflation E (ContinuousCohomology.π (galoisUnitsRep K E) 2 z) = x ∧
        let _ : NumberField E := NumberField.of_module_finite K E
        ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
          ∀ w : HeightOneSpectrum (𝓞 E), finitePlaceBelow (K := K) w ∉ S →
            Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal ∧
              (∀ a, w.valuation E (relativeCocycleValue E z a : E) = 1) := by
  obtain ⟨E, y, hy⟩ := exists_finiteInflation_eq x
  obtain ⟨z, rfl⟩ := ContinuousCohomology.π_surjective (galoisUnitsRep K E) 2 y
  refine ⟨E, z, hy, ?_⟩
  intro sharedNumberField
  exact exists_finite_exceptional_places K (relativeCocycleValue E z)

end ClassFieldTheory.Brauer

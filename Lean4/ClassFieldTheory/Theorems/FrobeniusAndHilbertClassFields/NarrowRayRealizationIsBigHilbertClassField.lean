import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.NarrowRayClassModulus
import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization
import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField
import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.ExistsRayArtinModulusProjection
import ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.BigHilbertClassFieldExists
import ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.BigHilbertClassFieldNarrowRayRealization

set_option autoImplicit false

/-!
# A narrow ray realization is a big Hilbert class field

The Frobenius-normalized realization of the narrow ray class group is
maximal among finite abelian extensions unramified at finite places.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

open NumberField IsDedekindDomain

/-- Every realization of the narrow ray class group is a big Hilbert class
field, including its maximality property. -/
theorem narrowRayRealization_isBigHilbertClassField
    (K : Type) [Field K] [NumberField K]
    (R : RayClassFieldRealization K (narrowRayClassModulus K)) :
    IsBigHilbertClassField R.extension := by
  obtain ⟨E, hE⟩ := exists_bigHilbertClassField K
  obtain ⟨S, hS⟩ := bigHilbertClassField_hasNarrowRayRealization K E hE
  subst E
  obtain ⟨f, _⟩ :=
    exists_rayArtin_modulusProjection
      (le_refl (narrowRayClassModulus K)) S R
  constructor
  · intro v
    exact R.unramifiedOutsideModulus.1 v (by simp [narrowRayClassModulus])
  · intro F hF
    obtain ⟨g⟩ := hE.2 F hF
    exact ⟨f.comp g⟩

end ClassFieldTheory

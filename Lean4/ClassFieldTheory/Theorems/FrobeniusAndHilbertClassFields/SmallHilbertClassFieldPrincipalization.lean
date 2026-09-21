import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
import ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison

set_option autoImplicit false

/-!
# Principalization in the small Hilbert class field

The principal ideal theorem says that extension to the Hilbert class field
makes every integral ideal of the base number field principal.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

/-- Every integral ideal becomes principal in a small Hilbert class field. -/
theorem ideals_becomePrincipalInSmallHilbertClassField
    (K : Type) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsSmallHilbertClassField E) :
    ∀ I : Ideal (𝓞 K),
      (I.map (algebraMap (𝓞 K) (𝓞 E))).IsPrincipal := by
  exact GlobalClassFieldComparison.ideals_becomePrincipalInSmallHilbertClassField_of_isSmall K E hE

end ClassFieldTheory

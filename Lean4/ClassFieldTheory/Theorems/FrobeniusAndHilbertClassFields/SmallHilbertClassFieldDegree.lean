import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsSmallHilbertClassField
import ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
import Mathlib.NumberTheory.NumberField.ClassNumber
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison

set_option autoImplicit false

/-!
# Degree of the small Hilbert class field

Any extension satisfying the intrinsic small-Hilbert-class-field property
has degree equal to the ordinary class number of the base field.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

/-- The small Hilbert class field has degree equal to the class number. -/
theorem smallHilbertClassField_degree_eq_classNumber
    (K : Type) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsSmallHilbertClassField E) :
    Module.finrank K E = NumberField.classNumber K :=
  GlobalClassFieldComparison.smallHilbertClassField_degree_eq_classNumber_of_isSmall K E hE

end ClassFieldTheory

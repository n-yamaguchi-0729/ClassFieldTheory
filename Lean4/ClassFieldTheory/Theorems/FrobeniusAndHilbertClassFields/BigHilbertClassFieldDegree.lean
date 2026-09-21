import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.NarrowRayClassModulus
import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField
import ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison

set_option autoImplicit false

/-!
# Degree of the big Hilbert class field

The degree of any extension satisfying the intrinsic big-Hilbert-class-field
property is the order of the narrow ray class group.  The latter is the ray
class group for the modulus containing every real place and no finite prime.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

/-- The big Hilbert class field has degree equal to the narrow class number. -/
theorem bigHilbertClassField_degree_eq_narrowClassGroup_card
    (K : Type) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsBigHilbertClassField E) :
    Module.finrank K E =
      Nat.card (RayClassGroup (narrowRayClassModulus K)) := by
  calc
    Module.finrank K E = Nat.card (RayClass.NarrowClassGroup K) :=
      GlobalClassFieldComparison.bigHilbertClassField_degree_eq_narrowClassGroup_card_of_isBig K E hE
    _ = Nat.card (RayClassGroup (narrowRayClassModulus K)) :=
      (Nat.card_congr
        (GlobalClassFieldComparison.narrowRayClassGroupEquivNarrowClassGroup K).toEquiv).symm

end ClassFieldTheory

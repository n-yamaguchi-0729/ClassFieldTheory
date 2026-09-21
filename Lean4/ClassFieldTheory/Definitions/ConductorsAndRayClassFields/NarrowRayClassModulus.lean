import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassModulus
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

set_option autoImplicit false

/-!
# The narrow class-group modulus
-/

noncomputable section

open scoped Classical

namespace ClassFieldTheory

universe u

/-- The modulus with no finite exponent and positivity at every real place.
Its ray class group is the narrow ideal class group. -/
def narrowRayClassModulus
    (K : Type u) [Field K] [NumberField K] : RayClassModulus K where
  finitePart := 0
  infinitePart := Finset.univ

end ClassFieldTheory

import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.OrdinaryRayClassModulus
import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.NarrowRayClassModulus

set_option autoImplicit false

/-!
# Ordinary and narrow moduli without real places
-/

namespace ClassFieldTheory

universe u

/-- If the base number field has no real places, the ordinary and narrow
class-group moduli coincide. -/
theorem ordinaryRayClassModulus_eq_narrow_of_noReal
    (K : Type u) [Field K] [NumberField K]
    [IsEmpty (RayClassRealPlace K)] :
    ordinaryRayClassModulus K = narrowRayClassModulus K := by
  classical
  have h : (Finset.univ : Finset (RayClassRealPlace K)) = ∅ := by
    ext v
    exact isEmptyElim v
  unfold ordinaryRayClassModulus narrowRayClassModulus
  rw [h]

end ClassFieldTheory

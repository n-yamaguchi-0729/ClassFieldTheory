import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization
import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup

set_option autoImplicit false

/-!
# Degree of a ray class field

For any ray class field realization of `m`, its degree is the cardinality of
the ideal-theoretic ray class group.  The realization is explicit, so this
module does not depend on an implementation-level choice of field.
-/

open scoped Classical NumberField

noncomputable section

namespace ClassFieldTheory

universe u

/-- The ray class field has degree equal to the ray class number. -/
theorem rayClassField_degree
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K)
    (R : RayClassFieldRealization K m) :
    Module.finrank K R.extension = Nat.card (RayClassGroup m) := by
  calc
    Module.finrank K R.extension =
        Nat.card (R.extension ≃ₐ[K] R.extension) :=
      (IsGalois.card_aut_eq_finrank K R.extension).symm
    _ = Nat.card (RayClassGroup m) :=
      Nat.card_congr R.artinEquiv.symm.toEquiv

end ClassFieldTheory

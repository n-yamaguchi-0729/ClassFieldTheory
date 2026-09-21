import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupRealization
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit false

/-!
# The quotient induced by a ray-class Artin map

The prescribed subgroup is identified with the Artin kernel before applying
the first isomorphism theorem.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u

/-- The isomorphism induced by the Artin map of a ray-class realization. -/
def rayClassSubgroupQuotientEquiv
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m))
    (R : RayClassSubgroupRealization K m H) :
    (RayClassGroup m ⧸ H) ≃* (R.extension ≃ₐ[K] R.extension) :=
  (QuotientGroup.quotientMulEquivOfEq R.artin_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      R.artin R.artin_surjective)

end ClassFieldTheory

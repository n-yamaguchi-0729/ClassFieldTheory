import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupQuotientEquiv

set_option autoImplicit false

/-!
# Evaluation of a ray-class subgroup quotient isomorphism

The quotient isomorphism retains the prescribed Artin normalization.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u

/-- A ray class maps to its original Artin value under the induced quotient isomorphism. -/
@[simp]
theorem rayClassSubgroupQuotientEquiv_mk
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m))
    (R : RayClassSubgroupRealization K m H)
    (x : RayClassGroup m) :
    rayClassSubgroupQuotientEquiv K m H R
        (QuotientGroup.mk' H x) = R.artin x := by
  rfl

end ClassFieldTheory

import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupRealization
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison

set_option autoImplicit false

/-!
# Existence of the class field of a ray-class subgroup

Every subgroup of an ideal-theoretic ray class group is the kernel of the
Frobenius-normalized Artin map of a finite abelian extension.  The statement
uses ideal classes; the proof transports the existing idelic reciprocity
construction to that interface.
-/

open scoped Classical NumberField

noncomputable section

namespace ClassFieldTheory

/-- Every ray-class subgroup has a finite abelian class-field realization. -/
theorem rayClassSubgroup_existence
    (K : Type) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m)) :
    Nonempty (RayClassSubgroupRealization K m H) := by
  exact GlobalClassFieldComparison.rayClassSubgroup_existence K m H

end ClassFieldTheory

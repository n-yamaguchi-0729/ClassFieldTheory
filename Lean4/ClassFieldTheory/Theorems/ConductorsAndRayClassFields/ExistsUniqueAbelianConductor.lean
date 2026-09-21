import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.ExistsAbelianConductor
import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.IsAbelianConductorUnique

set_option autoImplicit false

/-!
# Unique existence of the abelian conductor

Existence of a least ray-class-field modulus and uniqueness of any modulus
with the same universal property combine into a unique-existence statement.
-/

namespace ClassFieldTheory

/-- The conductor of a finite abelian extension of number fields exists
uniquely. -/
theorem existsUnique_abelianConductor
    (K : Type) [Field K] [NumberField K]
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L] :
    ∃! c : RayClassModulus K, IsAbelianConductor K L c := by
  obtain ⟨c, hc⟩ := exists_abelianConductor K L
  exact ⟨c, hc, fun d hd => hd.unique hc⟩

end ClassFieldTheory

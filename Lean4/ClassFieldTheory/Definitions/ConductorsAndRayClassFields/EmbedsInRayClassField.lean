import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization

set_option autoImplicit false

/-!
# Embedding into a ray class field
-/

namespace ClassFieldTheory

universe u v

/-- A finite extension embeds into a ray class field for `m`.  The existential
formulation avoids making a global choice of ray class field. -/
def EmbedsInRayClassField
    (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [NumberField L] [Algebra K L]
    (m : RayClassModulus K) : Prop :=
  ∃ R : RayClassFieldRealization K m,
    Nonempty (L →ₐ[K] R.extension)

end ClassFieldTheory

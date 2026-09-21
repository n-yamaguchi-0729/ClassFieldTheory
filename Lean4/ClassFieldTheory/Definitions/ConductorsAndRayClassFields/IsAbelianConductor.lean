import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.EmbedsInRayClassField

set_option autoImplicit false

/-!
# Conductors of finite abelian extensions
-/

namespace ClassFieldTheory

universe u v

/-- A modulus is the conductor of a finite abelian extension when it is
exactly the least modulus whose ray class field contains the extension. -/
def IsAbelianConductor
    (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [NumberField L] [Algebra K L]
    (c : RayClassModulus K) : Prop :=
  ∀ m : RayClassModulus K,
    EmbedsInRayClassField K L m ↔ c ≤ m

end ClassFieldTheory

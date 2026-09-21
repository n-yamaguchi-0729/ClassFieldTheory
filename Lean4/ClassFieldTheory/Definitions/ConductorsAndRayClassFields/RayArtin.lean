import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization

set_option autoImplicit false

/-!
# The ray Artin map
-/

noncomputable section

namespace ClassFieldTheory.RayClassFieldRealization

universe u

/-- The Frobenius-normalized ray Artin map. -/
def rayArtin
    {K : Type u} [Field K] [NumberField K]
    {m : RayClassModulus K}
    (R : RayClassFieldRealization K m) :
    RayClassGroup m →* (R.extension ≃ₐ[K] R.extension) :=
  R.artinEquiv.toMonoidHom

end ClassFieldTheory.RayClassFieldRealization

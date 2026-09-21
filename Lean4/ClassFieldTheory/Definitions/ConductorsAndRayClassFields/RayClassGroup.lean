import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassPrimeToIdeals
import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayPrincipalIdealSubgroup
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit false

/-!
# Ideal-theoretic ray class groups
-/

namespace ClassFieldTheory

universe u

/-- The ideal-theoretic ray class group of a modulus. -/
abbrev RayClassGroup
    {K : Type u} [Field K] [NumberField K]
    (m : RayClassModulus K) :=
  rayClassPrimeToIdeals m ⧸ rayPrincipalIdealSubgroupInPrimeTo m

/-- Ray class groups are multiplicatively commutative. -/
instance instIsMulCommutativeRayClassGroup
    {K : Type u} [Field K] [NumberField K]
    (m : RayClassModulus K) : IsMulCommutative (RayClassGroup m) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

end ClassFieldTheory

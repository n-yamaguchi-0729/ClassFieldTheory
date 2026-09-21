import ClassFieldTheory.Definitions.HilbertSymbols.PowerClass

set_option autoImplicit false

/-!
# Inversion of power classes

The quotient map to power classes preserves inverses.
-/

namespace ClassFieldTheory

universe u

/-- The class of an inverse is the inverse class. -/
@[simp]
theorem powerClass_inv
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ) :
    powerClass K n a⁻¹ = (powerClass K n a)⁻¹ :=
  map_inv (powerClass K n) a

end ClassFieldTheory

import ClassFieldTheory.Definitions.HilbertSymbols.PowerClass

set_option autoImplicit false

/-!
# Powers of power classes

The quotient map to power classes preserves powers.
-/

namespace ClassFieldTheory

universe u

/-- The class of a power is the corresponding power of the class. -/
@[simp]
theorem powerClass_pow
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ) (m : ℕ) :
    powerClass K n (a ^ m) = (powerClass K n a) ^ m :=
  map_pow (powerClass K n) a m

end ClassFieldTheory

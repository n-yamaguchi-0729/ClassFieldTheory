import ClassFieldTheory.Definitions.HilbertSymbols.PowerClass

set_option autoImplicit false

/-!
# Equality of power classes

Two representatives have the same power class precisely when their ratio
is an `n`-th power.
-/

namespace ClassFieldTheory

universe u

/-- Two elements represent the same power class exactly when their ratio is
an `n`-th power. -/
theorem powerClass_eq_iff
    (K : Type u) [Field K] (n : ℕ+) (a b : Kˣ) :
    powerClass K n a = powerClass K n b ↔
      a / b ∈ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  exact QuotientGroup.eq_iff_div_mem

end ClassFieldTheory

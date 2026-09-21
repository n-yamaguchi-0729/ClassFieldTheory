import ClassFieldTheory.Definitions.HilbertSymbols.PowerClassGroup

set_option autoImplicit false

/-!
# Canonical power classes
-/

namespace ClassFieldTheory

universe u

/-- The canonical class of a nonzero field element modulo `n`-th powers. -/
def powerClass (K : Type u) [Field K] (n : ℕ+) : Kˣ →* PowerClassGroup K n := by
  unfold PowerClassGroup
  exact QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range

end ClassFieldTheory

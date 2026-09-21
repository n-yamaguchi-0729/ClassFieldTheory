import ClassFieldTheory.Definitions.HilbertSymbols.PowerClass

set_option autoImplicit false

/-!
# Power-class laws and representatives

For a field `K` and a positive integer `n`, `PowerClassGroup K n` is the
quotient of `Kˣ` by the subgroup of `n`-th powers. A class is the identity
exactly when its representative belongs to the power subgroup.
-/

namespace ClassFieldTheory

universe u

/-- A power class is trivial exactly when its representative is an `n`-th
power. -/
@[simp]
theorem powerClass_eq_one_iff
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ) :
    powerClass K n a = 1 ↔
      a ∈ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  exact QuotientGroup.eq_one_iff a

end ClassFieldTheory

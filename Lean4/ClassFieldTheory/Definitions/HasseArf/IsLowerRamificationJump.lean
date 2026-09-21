import ClassFieldTheory.Definitions.HasseArf.LowerRamificationGroup

set_option autoImplicit false

/-!
# Lower ramification jumps
-/

namespace ClassFieldTheory

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

/-- A nonnegative integer `n` is a lower ramification jump when the lower
ramification filtration strictly changes after index `n`. -/
def IsLowerRamificationJump (A : ValuationSubring L) (n : ℕ) : Prop :=
  lowerRamificationGroup K A n ≠ lowerRamificationGroup K A (n + 1)

end ClassFieldTheory

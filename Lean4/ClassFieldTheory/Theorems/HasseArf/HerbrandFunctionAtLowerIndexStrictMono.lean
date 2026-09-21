import ClassFieldTheory.Definitions.HasseArf.HerbrandFunctionAtLowerIndex
import ClassFieldTheory.HasseArf
import Mathlib.Order.Monotone.Basic
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

/-!
# Strict growth of the integral-index Herbrand function

For a finite extension, each lower ramification group is finite and
nonempty. Thus every increment of the rational Herbrand function is
strictly positive. This does not assert integrality of its values.
-/

namespace ClassFieldTheory

universe u v

/-- The rational Herbrand function at nonnegative integral lower indices is
strictly increasing for a finite field extension. -/
theorem herbrandFunctionAtLowerIndex_strictMono
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (A : ValuationSubring L) :
    StrictMono (herbrandFunctionAtLowerIndex K A) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [herbrandFunctionAtLowerIndex_succ]
  have hnum : 0 < (Nat.card (lowerRamificationGroup K A (n + 1)) : ℚ) := by
    exact_mod_cast Nat.card_pos (α := lowerRamificationGroup K A (n + 1))
  have hden : 0 < (Nat.card (lowerRamificationGroup K A 0) : ℚ) := by
    exact_mod_cast Nat.card_pos (α := lowerRamificationGroup K A 0)
  exact lt_add_of_pos_right _ (div_pos hnum hden)

end ClassFieldTheory

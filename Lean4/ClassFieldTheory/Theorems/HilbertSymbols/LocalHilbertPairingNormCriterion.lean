import ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairing
import ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairingSymbol
import ClassFieldTheory.Definitions.HilbertSymbols.IsKummerNorm
import ClassFieldTheory.Definitions.HilbertSymbols.IsLocalHilbertPairing

set_option autoImplicit false

/-!
# Norm-residue criterion for a local Hilbert pairing

The vanishing of a local Hilbert symbol is equivalent to a concrete Kummer
norm condition.  The Kummer algebra is the canonical Mathlib quotient
`K[X] / (X^n - a)`, so the statement does not choose a root in an algebraic
closure.
-/

namespace ClassFieldTheory

universe u

/-- A local Hilbert pairing evaluates to one exactly on Kummer norms. -/
theorem localHilbertPairing_eq_one_iff_isKummerNorm
    (K : Type u) [Field K] (n : ℕ+)
    (B : HilbertPairing K n)
    (hB : HilbertPairing.IsLocalHilbertPairing B)
    (a b : Kˣ) :
    B.symbol a b = 1 ↔ IsKummerNorm K n a b := by
  exact hB.2.2.2 a b

end ClassFieldTheory

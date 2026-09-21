import ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairingSymbol
import ClassFieldTheory.Definitions.HilbertSymbols.IsKummerNorm

set_option autoImplicit false

/-!
# The norm-residue criterion
-/

namespace ClassFieldTheory.HilbertPairing

universe u

/-- The symbol of `a` and `b` is one exactly when `b` is a norm from the
Kummer algebra of `a`. -/
def SatisfiesNormResidueCriterion
    {K : Type u} [Field K] {n : ℕ+}
    (B : HilbertPairing K n) : Prop :=
  ∀ a b : Kˣ, B.symbol a b = 1 ↔ IsKummerNorm K n a b

end ClassFieldTheory.HilbertPairing

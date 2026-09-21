import ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairingSymbol

set_option autoImplicit false

/-!
# Hilbert-pairing symbol multiplication in the second argument

The symbol is multiplicative in its second representative.
-/

namespace ClassFieldTheory.HilbertPairing

universe u

/-- The symbol is multiplicative in its second representative. -/
@[simp]
theorem symbol_mul_right
    {K : Type u} [Field K] {n : ℕ+}
    (B : HilbertPairing K n) (a b c : Kˣ) :
    B.symbol a (b * c) = B.symbol a b * B.symbol a c := by
  simp only [symbol, map_mul]

end ClassFieldTheory.HilbertPairing

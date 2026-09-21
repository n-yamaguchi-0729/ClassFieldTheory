import ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairing
import ClassFieldTheory.Definitions.HilbertSymbols.PowerClass

set_option autoImplicit false

/-!
# Evaluation of a Hilbert pairing on representatives
-/

namespace ClassFieldTheory.HilbertPairing

universe u

/-- Evaluate a power-class pairing on representatives in `Kˣ`. -/
def symbol
    {K : Type u} [Field K] {n : ℕ+}
    (B : HilbertPairing K n) (a b : Kˣ) :
    rootsOfUnity (n : ℕ) K :=
  B (powerClass K n a) (powerClass K n b)

end ClassFieldTheory.HilbertPairing

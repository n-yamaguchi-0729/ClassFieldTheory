import ClassFieldTheory.Definitions.HilbertSymbols.PowerClassGroup
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option autoImplicit false

/-!
# Pairings on power classes
-/

namespace ClassFieldTheory

universe u

/-- Multiplicative pairings on `n`-th power classes with values in the
`n`-th roots of unity. -/
abbrev HilbertPairing (K : Type u) [Field K] (n : ℕ+) :=
  PowerClassGroup K n →*
    (PowerClassGroup K n →* rootsOfUnity (n : ℕ) K)

end ClassFieldTheory

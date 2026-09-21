import ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

set_option autoImplicit false

/-!
# Families of finite-place Hilbert pairings
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u

/-- A choice of power-class pairing on the completion of `F` at every finite
place.  No reciprocity law is hidden in this data type. -/
abbrev GlobalHilbertPairingFamily
    (F : Type u) [Field F] [NumberField F] (n : ℕ+) :=
  ∀ v : HeightOneSpectrum (𝓞 F), HilbertPairing (v.adicCompletion F) n

end ClassFieldTheory

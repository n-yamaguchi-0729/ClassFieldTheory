import ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairingSymbol

set_option autoImplicit false

/-!
# Algebraic laws for Hilbert pairings
-/

namespace ClassFieldTheory.HilbertPairing

universe u

/-- The Steinberg relation for a pairing on power classes. -/
def IsSteinberg
    {K : Type u} [Field K] {n : ℕ+}
    (B : HilbertPairing K n) : Prop :=
  ∀ (a : Kˣ) (ha : 1 - (a : K) ≠ 0),
    B.symbol a (Units.mk0 (1 - (a : K)) ha) = 1

/-- Skew-symmetry of a pairing on power classes. -/
def IsSkewSymmetric
    {K : Type u} [Field K] {n : ℕ+}
    (B : HilbertPairing K n) : Prop :=
  ∀ a b : PowerClassGroup K n, B a b = (B b a)⁻¹

/-- Nondegeneracy in both variables of a pairing on power classes. -/
def IsNondegenerate
    {K : Type u} [Field K] {n : ℕ+}
    (B : HilbertPairing K n) : Prop :=
  (∀ a : PowerClassGroup K n,
      (∀ b : PowerClassGroup K n, B a b = 1) → a = 1) ∧
    (∀ b : PowerClassGroup K n,
      (∀ a : PowerClassGroup K n, B a b = 1) → b = 1)

end ClassFieldTheory.HilbertPairing

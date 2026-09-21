import ClassFieldTheory.Definitions.HasseArf.RealLowerRamificationGroup
import ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups

set_option autoImplicit false

/-! # Real lower groups at natural indices -/

namespace ClassFieldTheory

universe u v

/-- The real lower group at a natural index is the original lower group. -/
theorem realLowerRamificationGroup_nat
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (n : ℕ) :
    realLowerRamificationGroup K A (n : ℝ) = lowerRamificationGroup K A n := by
  have hpow : (Int.ceil ((n : ℝ) + 1)).toNat = n + 1 :=
    RamificationTheory.HilbertRamification.Higher.realRamificationExponent_nat n
  apply Subgroup.ext
  intro σ
  change (∀ x : A,
      σ • x - x ∈ (IsLocalRing.maximalIdeal A) ^ (Int.ceil ((n : ℝ) + 1)).toNat) ↔
    (∀ x : A, σ • x - x ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1))
  rw [hpow]

end ClassFieldTheory

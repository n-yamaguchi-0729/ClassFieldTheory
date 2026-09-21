import ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairingLaws
import ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairingNormResidueCriterion

set_option autoImplicit false

/-!
# Local Hilbert pairings
-/

namespace ClassFieldTheory.HilbertPairing

universe u

/-- The algebraic laws and Kummer norm-residue criterion required of a local
Hilbert pairing.  These properties do not fix the value normalization of the
symbol; that requires a comparison with a normalized Artin map. -/
def IsLocalHilbertPairing
    {K : Type u} [Field K] {n : ℕ+}
    (B : HilbertPairing K n) : Prop :=
  B.IsSteinberg ∧ B.IsSkewSymmetric ∧ B.IsNondegenerate ∧
    B.SatisfiesNormResidueCriterion

end ClassFieldTheory.HilbertPairing

import KummerTheory.Concrete.Cyclotomic.ProfiniteUnitDecomposition.FiniteFree

/-!
# Compiled free-coordinate gathering stage of the profinite-unit decomposition
-/

open scoped Topology

noncomputable section

namespace KummerTheory.ProfiniteUnitDecomposition.Internal

open ClassFormation
open LocalFieldTheory.Padic

/-- Reassemble the family of local additive coordinates into `ℤ̂`. -/
noncomputable def gatherFree :
    ((p : Nat.Primes) → Multiplicative ℤ_[p.1]) ≃ₜ*
      Multiplicative ZHat :=
  (continuousPiMultiplicative
      (fun p : Nat.Primes => ℤ_[p.1])).symm.trans
    (continuousMultiplicativeEquivOfAddEquiv
      zHatContinuousAddEquivPrimeProduct).symm

end KummerTheory.ProfiniteUnitDecomposition.Internal

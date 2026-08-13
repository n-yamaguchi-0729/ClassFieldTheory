import KummerTheory.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Gather

/-!
# The profinite-unit product decomposition
-/

open scoped Topology

noncomputable section

namespace KummerTheory

open ClassFormation
open LocalFieldTheory.Padic

/-- Topological decomposition
`ℤ̂ˣ ≃ Multiplicative ℤ̂ × finite-product` used in the rational cyclotomic
calculation. -/
noncomputable def zHatUnitsDecomposition :
    ZHatˣ ≃ₜ* Multiplicative ZHat × CyclotomicFinitePart :=
  zHatUnitsContinuousMulEquivPrimeProduct.trans <|
    ProfiniteUnitDecomposition.Internal.localDecomposition.symm.trans <|
      ProfiniteUnitDecomposition.Internal.finiteFreeSplit.trans <|
        continuousMulEquivProdCongr
          ProfiniteUnitDecomposition.Internal.gatherFree
          (ContinuousMulEquiv.refl CyclotomicFinitePart)

end KummerTheory

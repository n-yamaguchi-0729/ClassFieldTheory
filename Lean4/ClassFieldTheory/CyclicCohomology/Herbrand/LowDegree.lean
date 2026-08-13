import Mathlib.SetTheory.Cardinal.Finite
import CyclicCohomology.TateH0
/-! Provides the public declarations in the `CyclicCohomology.Herbrand.LowDegree` Lean module. -/

namespace CyclicCohomology

open LocalFieldTheory

noncomputable section

/-- Degree-zero Tate cohomology of field units is equipotent to the norm quotient. -/
theorem herbrand_tateCohomology_zero_units_cardinal_eq_normQuotient (K L : Type)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Cardinal.mk (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0) =
      Cardinal.mk (Additive (NormQuotient K L)) :=
  Cardinal.mk_congr
    (H0TateUnitsIsoNormQuotient K L).toLinearEquiv.toEquiv

end
end CyclicCohomology

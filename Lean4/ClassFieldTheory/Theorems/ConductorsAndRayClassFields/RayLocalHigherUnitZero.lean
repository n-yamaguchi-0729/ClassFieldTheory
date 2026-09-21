import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayLocalHigherUnitGroup
import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Basic

set_option autoImplicit false

/-!
# The zeroth local higher-unit group
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTheory

universe u

open NumberField IsDedekindDomain

/-- At depth zero the local higher-unit group is the full group of
integral units, not the full multiplicative group of the local field. -/
theorem rayLocalHigherUnitGroup_zero
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    rayLocalHigherUnitGroup v 0 =
      (v.adicCompletionIntegers K).units := by
  change RayClass.localHigherUnitGroup v 0 =
    (v.adicCompletionIntegers K).units
  exact RayClass.localHigherUnitGroup_zero v

end ClassFieldTheory

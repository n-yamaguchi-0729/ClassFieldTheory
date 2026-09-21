import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.NumberFieldFractionalIdealGroup
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.DedekindDomain.Factorization

set_option autoImplicit false

/-!
# Fractional ideal represented by a finite prime
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u

/-- The nonzero fractional ideal represented by a finite prime. -/
def finitePrimeFractionalIdeal
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    NumberFieldFractionalIdealGroup K :=
  Units.mk0
    (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

end ClassFieldTheory

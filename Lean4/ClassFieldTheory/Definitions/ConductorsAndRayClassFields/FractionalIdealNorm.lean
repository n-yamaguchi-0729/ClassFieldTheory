import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.FractionalIdealNormExponentMap
import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.NumberFieldFractionalIdealFactorization

set_option autoImplicit false

/-!
# Relative norm of nonzero fractional ideals

The norm sends a finite-prime factor upstairs to the prime below it, with
exponent multiplied by the inertia degree. Prime factorization extends this
rule to a multiplicative map on all nonzero fractional ideals.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The relative norm of nonzero fractional ideals of number fields,
defined by its inertia-degree-weighted action on prime exponents. -/
def fractionalIdealNorm
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] :
    NumberFieldFractionalIdealGroup L →*
      NumberFieldFractionalIdealGroup K :=
  (NumberFieldFractionalIdealGroup.factorizationEquiv
      (K := K)).toMonoidHom.comp
    ((fractionalIdealNormExponentMap K L).toMultiplicative.comp
      (NumberFieldFractionalIdealGroup.factorizationEquiv
        (K := L)).symm.toMonoidHom)

end ClassFieldTheory

import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.FractionalIdealNorm
import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.FractionalIdealNormExponentMap
import ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.NumberFieldFractionalIdealFactorization

set_option autoImplicit false

/-!
# Prime exponents of a fractional-ideal norm

At a finite prime of the base, the exponent of the norm is the sum of the
upstairs exponents, each weighted by its inertia degree.  This is the
calculation needed when passing from ideals to norm-defined ray subgroups.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The exponent at `v` of an ideal norm is the inertia-degree-weighted sum
of the exponents at the primes lying above `v`. -/
theorem fractionalIdealNorm_primeExponent
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (I : NumberFieldFractionalIdealGroup L)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
        ((fractionalIdealNorm K L I : NumberFieldFractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      (NumberFieldFractionalIdealGroup.countVector I).sum fun W n =>
        if fractionalIdealNormPrimeBelow K L W = v then
          (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) * n
        else 0 := by
  classical
  have hcount :
      ((NumberFieldFractionalIdealGroup.factorizationEquiv
        (K := L)).symm I).toAdd =
        NumberFieldFractionalIdealGroup.countVector I := by
    ext W
    have h := NumberFieldFractionalIdealGroup.count_factorization
      ((NumberFieldFractionalIdealGroup.factorizationEquiv
        (K := L)).symm I) W
    have hfac :=
      (NumberFieldFractionalIdealGroup.factorizationEquiv
        (K := L)).apply_symm_apply I
    change NumberFieldFractionalIdealGroup.factorization
      ((NumberFieldFractionalIdealGroup.factorizationEquiv
        (K := L)).symm I) = I at hfac
    rw [hfac] at h
    exact h.symm.trans
      (NumberFieldFractionalIdealGroup.countVector_apply I W).symm
  change
    FractionalIdeal.count K v
        ((NumberFieldFractionalIdealGroup.factorization
          ((fractionalIdealNormExponentMap K L).toMultiplicative
            ((NumberFieldFractionalIdealGroup.factorizationEquiv
              (K := L)).symm I)) :
            NumberFieldFractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = _
  rw [NumberFieldFractionalIdealGroup.count_factorization]
  change fractionalIdealNormExponentMap K L
    ((NumberFieldFractionalIdealGroup.factorizationEquiv
      (K := L)).symm I).toAdd v = _
  rw [hcount]
  simp [fractionalIdealNormExponentMap, Finsupp.single_apply, eq_comm]

end ClassFieldTheory

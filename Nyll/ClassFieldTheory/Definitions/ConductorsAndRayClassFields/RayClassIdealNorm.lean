/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.FractionalIdealFactorization
public import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.FractionalIdealNorm
public import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.FinitePlaceContraction

/-!
# Ideal norms in an ideal-theoretic ray class group

The domain consists of fractional ideals of `L` with zero valuation at every
prime lying above the finite support of `m`.  The relative ideal norm maps
this group into the fractional ideals of `K` prime to `m`; composing with the
ray quotient gives its genuine ideal-norm image.  This construction does not
identify ideal norms with idèle-class norms.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u v

/-- Fractional ideals upstairs prime to the primes above a base ray modulus. -/
def rayClassPrimeToIdealNormDomain
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (m : RayClassModulus K) :
    Subgroup (NumberFieldFractionalIdealGroup L) :=
  FractionalIdealFactorization.primeTo (F := L)
    {W | _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support}

open scoped Classical in
/-- The exponent of a relative fractional-ideal norm at a finite prime is
the inertia-degree-weighted sum of the exponents at the primes above it. -/
theorem fractionalIdealNorm_count
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (I : NumberFieldFractionalIdealGroup L)
    (w : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K w
        ((fractionalIdealNorm K L I : NumberFieldFractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      (NumberFieldFractionalIdealGroup.countVector I).sum fun W n =>
        if _root_.finitePlaceBelow (K := K) W = w then
          (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) * n else 0 := by
  let e := (NumberFieldFractionalIdealGroup.factorizationEquiv
    (K := L)).symm I
  have he : e.toAdd = NumberFieldFractionalIdealGroup.countVector I :=
    NumberFieldFractionalIdealGroup.factorizationEquiv_symm_toAdd I
  change FractionalIdeal.count K w
      ((NumberFieldFractionalIdealGroup.factorization (K := K)
        (Multiplicative.ofAdd
          (fractionalIdealNormExponentMap K L e.toAdd)) :
        NumberFieldFractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = _
  rw [NumberFieldFractionalIdealGroup.count_factorization]
  change fractionalIdealNormExponentMap K L e.toAdd w = _
  rw [he]
  exact fractionalIdealNormExponentMap_apply K L
    (NumberFieldFractionalIdealGroup.countVector I) w

/-- The genuine fractional-ideal norm, restricted to ideals prime to the
finite support of a base ray modulus. -/
def rayClassPrimeToIdealNorm
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (m : RayClassModulus K) :
    rayClassPrimeToIdealNormDomain K L m →*
      rayClassPrimeToIdeals m where
  toFun I := ⟨fractionalIdealNorm K L I, by
    classical
    intro w hw
    rw [fractionalIdealNorm_count K L I w]
    apply Finset.sum_eq_zero
    intro W _
    by_cases hbelow : _root_.finitePlaceBelow (K := K) W = w
    · have hW : W ∈ {W | _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support} := by
        change _root_.finitePlaceBelow (K := K) W ∈ m.finitePart.support
        rw [hbelow]
        exact hw
      dsimp only
      rw [ite_eq_left hbelow,
        NumberFieldFractionalIdealGroup.countVector_apply,
        I.property W hW]
      simp only [mul_zero]
    · dsimp only
      rw [ite_eq_right hbelow]⟩
  map_one' := by
    apply Subtype.ext
    change fractionalIdealNorm K L 1 = 1
    exact map_one (fractionalIdealNorm K L)
  map_mul' I J := by
    apply Subtype.ext
    change fractionalIdealNorm K L
        ((I : NumberFieldFractionalIdealGroup L) * J) =
      fractionalIdealNorm K L I * fractionalIdealNorm K L J
    exact map_mul (fractionalIdealNorm K L)
      (I : NumberFieldFractionalIdealGroup L)
      (J : NumberFieldFractionalIdealGroup L)

/-- The relative ideal norm followed by the ideal-theoretic ray quotient. -/
def rayClassIdealNorm
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (m : RayClassModulus K) :
    rayClassPrimeToIdealNormDomain K L m →* RayClassGroup m :=
  (QuotientGroup.mk' (rayPrincipalIdealSubgroupInPrimeTo m)).comp
    (rayClassPrimeToIdealNorm K L m)

/-- The actual ideal-norm subgroup of the ray class group.  Its equality
with an Artin kernel is a separate reciprocity theorem. -/
def rayClassIdealNormImage
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (m : RayClassModulus K) : Subgroup (RayClassGroup m) :=
  (rayClassIdealNorm K L m).range

end ClassFieldTheory

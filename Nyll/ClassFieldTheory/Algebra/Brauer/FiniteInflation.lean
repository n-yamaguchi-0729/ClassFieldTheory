/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.Galois.Profinite
public import Nyll.ClassFieldTheory.Algebra.Brauer.Restriction

/-!
# Finite inflation into the cohomological Brauer group

A finite Galois subextension of a separable closure supplies the original
restriction of automorphisms and inclusion of units.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace ClassFieldTheory.Brauer

variable {K : Type u} [Field K]

/-- The continuous quotient map to the Galois group of the given finite subextension. -/
def finiteGaloisRestriction (E : FiniteGaloisIntermediateField K (SeparableClosure K)) :
    Gal(SeparableClosure K/K) →ₜ* Gal(E/K) where
  toMonoidHom := AlgEquiv.restrictNormalHom E.toIntermediateField
  continuous_toFun := InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField

/-- The quotient map acts by the usual restriction of the original automorphism. -/
theorem finiteGaloisRestriction_commutes
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (σ : Gal(SeparableClosure K/K)) (x : E) :
    (finiteGaloisRestriction E σ x : SeparableClosure K) = σ (x : SeparableClosure K) :=
  σ.restrictNormal_commutes E.toIntermediateField x

/-- The finite-stage unit group acts on its actual units inside the separable closure. -/
def finiteInflationCoefficientMap (E : FiniteGaloisIntermediateField K (SeparableClosure K)) :
    TopRep.res (finiteGaloisRestriction E).toMonoidHom (galoisUnitsRep K E) ⟶ unitsRep K :=
  galoisUnitsMap (finiteGaloisRestriction E) E.toIntermediateField.val.toRingHom
    (finiteGaloisRestriction_commutes E)

/-- The relative group in the continuous presentation of the finite Galois group. -/
abbrev relativeBr (E : FiniteGaloisIntermediateField K (SeparableClosure K)) : Type u :=
  continuousCohomology 2 (galoisUnitsRep K E)

/-- Inflation from the given finite Galois subextension on the original
continuous cochains in every degree. -/
def finiteDegreeInflation (E : FiniteGaloisIntermediateField K (SeparableClosure K)) (n : ℕ) :
    continuousCohomology n (galoisUnitsRep K E) →+ continuousCohomology n (unitsRep K) :=
  transportCohomology n (finiteGaloisRestriction E) E.toIntermediateField.val.toRingHom
    (finiteGaloisRestriction_commutes E)

/-- Degree-two inflation from the given finite Galois subextension. -/
def finiteInflation (E : FiniteGaloisIntermediateField K (SeparableClosure K)) :
    relativeBr E →+ Br K :=
  finiteDegreeInflation E 2

/-- Inflating a relative class inflates its original cocycle. -/
theorem finiteDegreeInflation_π (E : FiniteGaloisIntermediateField K (SeparableClosure K)) (n : ℕ)
    (z : ContinuousCohomology.cocycles (galoisUnitsRep K E) n) :
    finiteDegreeInflation E n (ContinuousCohomology.π (galoisUnitsRep K E) n z) =
      ContinuousCohomology.π (unitsRep K) n
        (ContinuousCohomology.cocyclesMap
          (finiteGaloisRestriction E) (finiteInflationCoefficientMap E) n z) :=
  ConcreteCategory.congr_hom
    (ContinuousCohomology.π_map (finiteGaloisRestriction E) (finiteInflationCoefficientMap E) n) z

/-- Degree-two inflation takes the class of the original inflated cocycle. -/
theorem finiteInflation_π (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (z : ContinuousCohomology.cocycles (galoisUnitsRep K E) 2) :
    finiteInflation E (ContinuousCohomology.π (galoisUnitsRep K E) 2 z) =
      ContinuousCohomology.π (unitsRep K) 2
        (ContinuousCohomology.cocyclesMap
          (finiteGaloisRestriction E) (finiteInflationCoefficientMap E) 2 z) :=
  finiteDegreeInflation_π E 2 z

end ClassFieldTheory.Brauer

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.LiftedUnitsCohomology
public import Nyll.GaloisCohomology.Kummer.UnitsCohomologyCongr
public import Nyll.GaloisCohomology.GroupTheory.CoefficientRingEquivalence
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Transport of actual unit cohomology with lifted integer coefficients

Both comparisons use the specified field equivalence or scalar restriction.
The units and their automorphism actions are the original ones.
-/

@[expose] public section

universe u v w
open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

/-- The given field equivalence on units, linear for the transported integer action. -/
def liftedUnitsMapEquivLinear
    (K : Type v) (L M : Type u) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    (e : L ≃ₐ[K] M) :
    liftedGaloisUnitsRep K L ≃ₗ[ULift.{u} ℤ] liftedGaloisUnitsRep K M :=
  LinearEquiv.ofBijective
    (ModuleCat.coefficientRingAddHom
      (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ)
      (M := ModuleCat.of ℤ (Additive Lˣ)) (N := ModuleCat.of ℤ (Additive Mˣ))
      (Units.mapEquiv e.toMulEquiv).toAdditive.toAddMonoidHom).hom
    (Units.mapEquiv e.toMulEquiv).toAdditive.bijective

/-- The original top-field equivalence induces the actual lifted unit-cohomology map. -/
def liftedUnitsCohomologyCongrTop
    (K : Type v) (L M : Type u) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    (e : L ≃ₐ[K] M) (n : ℕ) :
    groupCohomology (liftedGaloisUnitsRep K L) n ≅
      groupCohomology (liftedGaloisUnitsRep K M) n :=
  groupCohomology.mapIso (AlgEquiv.autCongr e) (liftedUnitsMapEquivLinear K L M e) (by
    intro σ
    apply LinearMap.ext
    intro x
    exact unitsMapEquiv_action K L M e σ x) n

/-- Surjective base-field scalar restriction leaves the upper units and action unchanged. -/
def liftedUnitsCohomologyRestrictScalarsIso
    (F : Type v) (E : Type w) (N : Type u) [Field F] [Field E] [Field N]
    [Algebra F E] [Algebra E N] [Algebra F N] [IsScalarTower F E N]
    (h : Function.Surjective (algebraMap F E)) (n : ℕ) :
    groupCohomology (liftedGaloisUnitsRep E N) n ≅
      groupCohomology (liftedGaloisUnitsRep F N) n :=
  groupCohomology.mapIso
    (AlgEquiv.extendScalarsHomOfSurjective (A := N) h).symm
    (LinearEquiv.refl (ULift.{u} ℤ) (Additive Nˣ)) (fun _ => rfl) n

end
end ClassFieldTower.Cohomology

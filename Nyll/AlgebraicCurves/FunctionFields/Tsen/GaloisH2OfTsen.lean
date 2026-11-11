/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.FunctionFields.Tsen.PGroupH2OfTsen
public import Nyll.GaloisCohomology.GroupTheory.H2FiniteIndexTrace
public import Nyll.GaloisCohomology.Kummer.LiftedUnitsCohomology
public import Nyll.GaloisCohomology.GroupTheory.CoefficientRingEquivalence

/-!
# Unit H² of arbitrary finite Galois extensions of curve function fields

The Sylow fixed fields remain one-variable function fields. Their relative Galois
groups are p-groups, so the previously proved vanishing applies. The finite-index
trace detects vanishing in the original actual group-cohomology object.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicCurve

open ClassFieldTower.Cohomology

/-- Actual unit H² vanishes for every finite Galois extension of a one-variable
function field over an algebraically closed field. -/
theorem liftedGaloisUnitsH2_eq_zero_of_transcendental_of_finiteDimensional
    (K : Type u) [Field K] [IsAlgClosed K] {F : Type u} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (E : Type u) [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (c : groupCohomology (liftedGaloisUnitsRep F E) 2) : c = 0 := by
  apply H2_eq_zero_of_sylow_restrictions_isZero
    (liftedGaloisUnitsRep F E) ?_ c
  intro p hp P
  let L : IntermediateField F E := IntermediateField.fixedField (P : Subgroup Gal(E/F))
  let : Algebra K L := ((algebraMap F L).comp (algebraMap K F)).toAlgebra
  have : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsGalois L E := IsGalois.of_fixed_field E (P : Subgroup Gal(E/F))
  have hP : IsPGroup p Gal(E/L) :=
    P.isPGroup'.of_equiv (IntermediateField.subgroupEquivAlgEquiv
      (P : Subgroup Gal(E/F)))
  obtain ⟨y, hy, hyfin, _⟩ :=
    exists_separating_transcendental_over_finite_extension K x hx hfin L
  have hz (a : groupCohomology (liftedGaloisUnitsRep L E) 2) : a = 0 :=
    liftedPGroupUnitsH2_eq_zero_of_transcendental_of_finiteDimensional K y hy hyfin p E hP a
  let : Subsingleton (groupCohomology (liftedGaloisUnitsRep L E) 2) :=
    ⟨fun a b => (hz a).trans (hz b).symm⟩
  have hzero : Limits.IsZero (groupCohomology (liftedGaloisUnitsRep L E) 2) :=
    ModuleCat.isZero_of_subsingleton _
  have heq : L.fixingSubgroup = (P : Subgroup Gal(E/F)) :=
    IntermediateField.fixingSubgroup_fixedField (P : Subgroup Gal(E/F))
  change Limits.IsZero (groupCohomology
    (Rep.res (P : Subgroup Gal(E/F)).subtype (liftedGaloisUnitsRep F E)) 2)
  rw [← heq]
  exact hzero.of_iso
    (liftedFiniteGaloisUnitsRelativeCohomologyIso F E L 2)

/-- The original integer-coefficient formulation, transported through the
coefficient-complex isomorphism from native lifted unit cohomology. -/
theorem galoisUnitsH2_eq_zero_of_transcendental_of_finiteDimensional
    (K : Type) [Field K] [IsAlgClosed K] {F : Type} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (c : groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2) : c = 0 := by
  let e := groupCohomology.coefficientRingIso
    (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ) (Rep.ofAlgebraAutOnUnits F E) 2
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  change e.hom.hom c = e.hom.hom 0
  rw [e.hom.hom.map_zero]
  exact liftedGaloisUnitsH2_eq_zero_of_transcendental_of_finiteDimensional
    K x hx hfin E (e.hom.hom c)

end AlgebraicCurve

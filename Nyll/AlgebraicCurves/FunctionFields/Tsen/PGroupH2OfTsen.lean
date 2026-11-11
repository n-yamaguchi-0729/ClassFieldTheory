/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.FunctionFields.Tsen.NormSurjectiveOfTsen
public import Nyll.GaloisCohomology.Kummer.LiftedUnitsCohomology
public import Nyll.GaloisCohomology.GroupTheory.PGroupGaloisTower
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Nyll.GaloisCohomology.GroupTheory.CoefficientRingEquivalence

/-!
# Unit H² of finite Galois p-extensions of curve function fields

A central prime-order subgroup supplies an actual intermediate field.
Tsen kills the cyclic upper extension, induction kills the lower extension,
and the existing unit H² inflation-restriction exactness kills the original class.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicCurve

open ClassFieldTower.Cohomology

/-- Actual unit-coefficient H² vanishes for finite Galois p-extensions of
one-variable function fields over algebraically closed fields. -/
theorem liftedPGroupUnitsH2_eq_zero_of_transcendental_of_finiteDimensional
    (K : Type u) [Field K] [IsAlgClosed K] {F : Type u} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (p : ℕ) [Fact p.Prime]
    (E : Type u) [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (hP : IsPGroup p Gal(E/F))
    (c : groupCohomology (liftedGaloisUnitsRep F E) 2) : c = 0 := by
  generalize hn : Module.finrank F E = n
  induction n using Nat.strong_induction_on generalizing E with
  | h n ih =>
    rcases subsingleton_or_nontrivial Gal(E/F) with hTrivial | hNontrivial
    · have : Subsingleton (groupCohomology (liftedGaloisUnitsRep F E) 2) :=
        ModuleCat.isZero_iff_subsingleton.mp
          (isZero_groupCohomology_succ_of_subsingleton
            (liftedGaloisUnitsRep F E) 1)
      exact Subsingleton.elim _ _
    · obtain ⟨L, hBase, hTop, hBaseP, hCyclic, _, hSmaller, _⟩ :=
        IsGalois.exists_intermediateField_prime_degree_of_isPGroup F E p hP
      let : Algebra K L :=
        ((algebraMap F L).comp (algebraMap K F)).toAlgebra
      have : IsScalarTower K F L :=
        IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      have hUpper :
          (liftedFiniteGaloisUnitsH2Restriction F E L).hom c = 0 :=
        liftedCyclicUnitsH2_eq_zero_of_norm_surjective L E
          (norm_surjective_over_finite_extension K x hx hfin L E) _
      obtain ⟨b, hb⟩ :=
        liftedFiniteGaloisUnitsH2Restriction_ker_le_inflation_range
          F E L hUpper
      have hb0 : b = 0 :=
        ih (Module.finrank F L) (hn ▸ hSmaller) L hBaseP b rfl
      rw [← hb, hb0, map_zero]

/-- The original integer-coefficient formulation, transported through the
coefficient-complex isomorphism from native lifted unit cohomology. -/
theorem pGroupUnitsH2_eq_zero_of_transcendental_of_finiteDimensional
    (K : Type) [Field K] [IsAlgClosed K] {F : Type} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (hP : IsPGroup p Gal(E/F))
    (c : groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2) : c = 0 := by
  let e := groupCohomology.coefficientRingIso
    (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ) (Rep.ofAlgebraAutOnUnits F E) 2
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  change e.hom.hom c = e.hom.hom 0
  rw [e.hom.hom.map_zero]
  exact liftedPGroupUnitsH2_eq_zero_of_transcendental_of_finiteDimensional
    K x hx hfin p E hP (e.hom.hom c)

end AlgebraicCurve

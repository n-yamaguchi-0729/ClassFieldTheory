/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.DiscreteRelative
public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteBaseChange
public import Nyll.GaloisCohomology.Kummer.UnitsPrimitiveDescent

/-! # Injectivity and compatibility of finite-stage Brauer inflation -/

@[expose] public section

open CategoryTheory TopRep ContinuousCohomology ClassFieldTower.Cohomology
open scoped Topology

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

variable {K : Type u} [Field K]

private theorem inflatedBoundary_value (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (z : cocycles (galoisUnitsRep K E) 2) (b : (homogeneousCochains (unitsRep K)).X 1)
    (hb : ((homogeneousCochains (unitsRep K)).d 1 2).hom b =
      (homogeneousCochains (unitsRep K)).iCycles 2
        (cocyclesMap (finiteGaloisRestriction E) (finiteInflationCoefficientMap E) 2 z))
    (σ τ : Gal(SeparableClosure K/K)) :
    let B : Gal(SeparableClosure K/K) → Rep.ofAlgebraAutOnUnits K (SeparableClosure K) :=
      fun g => b.val 1 g
    (Rep.ofAlgebraAutOnUnits K (SeparableClosure K)).ρ σ (B τ) - B (σ * τ) + B σ =
        unitsInclusion K (SeparableClosure K) E.toIntermediateField
          (dehomogenizeIntegralTwo (galoisUnitsRep K E) z
            (finiteGaloisRestriction E σ, finiteGaloisRestriction E τ)) := by
  intro B
  let X := galoisUnitsRep K E
  let Y := unitsRep K
  let D := homogeneousCochains Y
  let r := finiteGaloisRestriction E
  let φ := finiteInflationCoefficientMap E
  let z₀ := (homogeneousCochains X).iCycles 2 z
  let w := cocyclesMap r φ 2 z
  have h₁ : r (1 : Gal(SeparableClosure K/K)) = 1 := map_one r
  have h₂ : r (σ * τ) = r σ * r τ := map_mul r σ τ
  have ha : z₀.val (r 1) (r σ) (r (σ * τ)) = z₀.val 1 (r σ) (r σ * r τ) := by
    rw [h₁, h₂]
  have hmap : (D.iCycles 2 w).val 1 σ (σ * τ) = φ (z₀.val (r 1) (r σ) (r (σ * τ))) :=
    mappedRelativeCocycle_apply r φ z 1 σ (σ * τ)
  have hboundary := congrArg (fun q : D.X 2 => q.val 1 σ (σ * τ)) hb
  have hdehom := dehomogenizeBoundary_one_apply Y b σ τ
  have hargs := congrArg (fun a : X => φ a) ha
  change groupCohomology.d₁₂ (underlyingIntegralRep Y) B (σ, τ) = _
  exact (((hdehom.symm.trans hboundary).trans hmap).trans hargs).trans rfl

private theorem relativeClass_eq_zero_of_locallyConstantPrimitive
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (z : cocycles (galoisUnitsRep K E) 2)
    (b : Gal(SeparableClosure K/K) → Rep.ofAlgebraAutOnUnits K (SeparableClosure K))
    (hB : IsLocallyConstant b)
    (hδ : ∀ σ τ : Gal(SeparableClosure K/K),
      (Rep.ofAlgebraAutOnUnits K (SeparableClosure K)).ρ σ (b τ) - b (σ * τ) + b σ =
        unitsInclusion K (SeparableClosure K) E.toIntermediateField
          (dehomogenizeIntegralTwo (galoisUnitsRep K E) z
            (finiteGaloisRestriction E σ, finiteGaloisRestriction E τ))) :
    π (galoisUnitsRep K E) 2 z = 0 := by
  let X := galoisUnitsRep K E
  let c := dehomogenizeIntegralTwo X z
  obtain ⟨a, ha⟩ := unitsPrimitiveDescends_of_isLocallyConstant K (SeparableClosure K)
    E.toIntermediateField c (groupCohomology.cocycles₂_map_one_snd c)
    (groupCohomology.cocycles₂_map_one_fst c) b hB hδ
  apply (continuousRelativeUnitsH2Equiv K E).injective
  rw [map_zero]
  change discreteIntegralH2Hom X (π X 2 z) = 0
  exact (discreteIntegralH2Hom_π X z).trans
    ((groupCohomology.H2π_eq_zero_iff c).mpr ⟨a, funext fun p => ha p.1 p.2⟩)

/-- Absolute inflation is faithful on actual finite relative Brauer classes.
If the inflated representative is a boundary, its continuous primitive
descends after the Hilbert 90 correction. -/
theorem finiteInflation_injective (E : FiniteGaloisIntermediateField K (SeparableClosure K)) :
    Function.Injective (finiteInflation E) := by
  apply (injective_iff_map_eq_zero (finiteInflation E)).mpr
  intro x hx
  obtain ⟨z, rfl⟩ := π_surjective (galoisUnitsRep K E) 2 x
  let w := cocyclesMap (finiteGaloisRestriction E) (finiteInflationCoefficientMap E) 2 z
  have hw : π (unitsRep K) 2 w = 0 := (finiteInflation_π E z).symm.trans hx
  obtain ⟨b, hb⟩ := exists_boundary_of_π_eq_zero (unitsRep K) 1 w hw
  let B : Gal(SeparableClosure K/K) → Rep.ofAlgebraAutOnUnits K (SeparableClosure K) :=
    fun σ => b.val 1 σ
  have hB : IsLocallyConstant B :=
    (IsLocallyConstant.iff_continuous (b.val 1)).mpr (b.val 1).continuous
  exact relativeClass_eq_zero_of_locallyConstantPrimitive E z B hB (inflatedBoundary_value E z b hb)

/-- Enlarging the finite stage through an actual inclusion does not change
absolute inflation. The hypothesis identifies the composite of the given
algebra map and the literal upper inclusion with the literal lower inclusion. -/
theorem finiteInflation_tower (E F : FiniteGaloisIntermediateField K (SeparableClosure K))
    [Algebra E F] [IsScalarTower K E F]
    (hinc : ∀ x : E, F.toIntermediateField.val (algebraMap E F x) = E.toIntermediateField.val x)
    (x : relativeBr E) :
    finiteInflation F (relativeInflation K E F x) = finiteInflation E x := by
  let rE := finiteGaloisRestriction E
  let rF := finiteGaloisRestriction F
  let rEF := finiteRelativeRestriction K E F
  let φE := finiteInflationCoefficientMap E
  let φF := finiteInflationCoefficientMap F
  let φEF := relativeInflationCoefficientMap K E F
  have hr (σ : Gal(SeparableClosure K/K)) : rEF (rF σ) = rE σ := by
    apply AlgEquiv.ext
    intro a
    apply E.toIntermediateField.val.injective
    calc
      E.toIntermediateField.val (rEF (rF σ) a) =
        F.toIntermediateField.val (algebraMap E F (rEF (rF σ) a)) := (hinc _).symm
      _ = F.toIntermediateField.val (rF σ (algebraMap E F a)) := by
        exact congrArg F.toIntermediateField.val ((rF σ).restrictNormal_commutes E a)
      _ = σ (F.toIntermediateField.val (algebraMap E F a)) :=
        finiteGaloisRestriction_commutes F σ (algebraMap E F a)
      _ = σ (E.toIntermediateField.val a) := congrArg σ (hinc a)
      _ = E.toIntermediateField.val (rE σ a) := (finiteGaloisRestriction_commutes E σ a).symm
  have h := galoisUnitsCohomologyMap_comp rEF rF rE
    (algebraMap E F) F.toIntermediateField.val.toRingHom E.toIntermediateField.val.toRingHom
    (fun σ a => σ.restrictNormal_commutes E a) (finiteGaloisRestriction_commutes F)
    (finiteGaloisRestriction_commutes E) hr hinc
  change map rF φF 2 (map rEF φEF 2 x) = map rE φE 2 x
  exact (ConcreteCategory.congr_hom h x).symm

end ClassFieldTheory.Brauer

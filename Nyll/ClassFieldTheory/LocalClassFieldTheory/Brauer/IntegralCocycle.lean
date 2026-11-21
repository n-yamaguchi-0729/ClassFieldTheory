/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.DiscreteRelative
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.Cohomology
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.Norm
public import Nyll.GaloisCohomology.ProP.FiniteCyclicH2CoefficientNorm

/-! # Vanishing of unramified integral-unit Brauer cocycles -/

@[expose] public section

noncomputable section

open scoped ValuativeRel
open CategoryTheory ClassFieldTower.Cohomology CyclicCohomology.ProfiniteCohomology.Herbrand
open LocalClassFieldTheory LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField

namespace ClassFieldTheory.Brauer

universe u

private theorem ordinaryH2_eq_zero_of_values_in_range {R G : Type u} [CommRing R] [Group G]
    {A B : Rep R G} (ι : A ⟶ B) (hι : Function.Injective (fun a : A => ι a))
    (c : groupCohomology.cocycles₂ B) (hcoeff : ∀ p, ∃ a : A, ι a = c p)
    (hzero : ∀ x : groupCohomology A 2, x = 0) :
    groupCohomology.H2π B c = 0 := by
  let d (p : G × G) : A := (hcoeff p).choose
  have hd (p : G × G) : ι (d p) = c p := (hcoeff p).choose_spec
  let r := MonoidHom.id G
  have hcochain : groupCohomology.cochainsMap₂ r ι d = c := funext hd
  have hc0 : (groupCohomology.d₂₃ B).hom c = 0 := c.property
  have hdcycle : d ∈ groupCohomology.cocycles₂ A := by
    rw [groupCohomology.cocycles₂, LinearMap.mem_ker]
    funext p
    apply hι
    have hcomm := ConcreteCategory.congr_hom (groupCohomology.mapShortComplexH2 r ι).comm₂₃ d
    have h := (congrFun hcomm p).symm
    change ι (((groupCohomology.d₂₃ A).hom d) p) =
      ((groupCohomology.d₂₃ B).hom (groupCohomology.cochainsMap₂ r ι d)) p at h
    rw [hcochain, hc0] at h
    exact h.trans ι.hom.toLinearMap.map_zero.symm
  let z : groupCohomology.cocycles₂ A := ⟨d, hdcycle⟩
  have hc : groupCohomology.mapCocycles₂ r ι z = c := Subtype.ext hcochain
  have hπ := congrArg (fun w : groupCohomology.cocycles₂ B => groupCohomology.H2π B w) hc.symm
  have hmap := groupCohomology.H2π_comp_map_apply r ι z
  let f := groupCohomology.map r ι 2
  have hz : f (groupCohomology.H2π A z) = 0 :=
    (congrArg (fun w : groupCohomology A 2 => f w) (hzero _)).trans f.hom.map_zero
  exact hπ.trans (hmap.symm.trans hz)

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]

private def integerUnitsStandardRep : Rep.{u} ℤ Gal(L/K) :=
  let : MulDistribMulAction (Gal(L/K)) 𝒪[L]ˣ :=
    galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ

private abbrev integerUnitsRep : Rep.{u} (ULift.{u} ℤ) Gal(L/K) :=
  (IntegralGroupCohomology.coefficientFunctor Gal(L/K)).obj (integerUnitsStandardRep K L)

private def integerUnitCoefficientMap : integerUnitsRep K L ⟶ liftedGaloisUnitsRep K L :=
  (IntegralGroupCohomology.coefficientFunctor Gal(L/K)).map
    (Rep.ofHom {
      toLinearMap := (integerUnitsToFieldUnits L).toAdditive.toIntLinearMap
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro a
        exact congrArg Additive.ofMul
          (integerUnitsToFieldUnits_galoisGroup_equivariant K L g
            (show Additive 𝒪[L]ˣ from a).toMul) })

private theorem integerUnitCoefficientMap_apply (a : integerUnitsRep K L) :
    integerUnitCoefficientMap K L a =
      Additive.ofMul (integerUnitsToFieldUnits L (show Additive 𝒪[L]ˣ from a).toMul) := rfl

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [FiniteDimensional K L] [IsGalois K L]
    [Module.Finite 𝒪[K] 𝒪[L]] [IsUnramifiedValuedExtension K L]

private theorem integerUnitsH2_eq_zero (x : groupCohomology (integerUnitsRep K L) 2) : x = 0 := by
  let : MulDistribMulAction (Gal(L/K)) 𝒪[L]ˣ :=
    galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  let : IsCyclic Gal(L/K) := isCyclic_galoisGroup_of_unramifiedValuation K L
  let : CommGroup Gal(L/K) := IsCyclic.commGroup
  let g := arithmeticFrobeniusOfUnramifiedValuation K L
  let hg := arithmeticFrobeniusOfUnramifiedValuation_generates K L
  let A := integerUnitsRep K L
  obtain ⟨a, rfl⟩ := finiteCyclicGroupH2_piEven_surjective A g hg x
  apply (Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff A g hg 2 (by decide) a).mpr
  have hcycle := a.property
  change A.ρ g a.val - a.val = 0 at hcycle
  have ha : A.ρ g a.val = a.val := sub_eq_zero.mp hcycle
  have hfix (σ : Gal(L/K)) : σ • (show Additive 𝒪[L]ˣ from a.val).toMul =
      (show Additive 𝒪[L]ˣ from a.val).toMul :=
    congrArg Additive.toMul
      ((Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg a.val).mpr ha σ)
  obtain ⟨b, hb⟩ := exists_integerUnit_map_eq_of_galoisGroup_fixed K L _ hfix
  obtain ⟨c, hc⟩ := normIntegerUnits_surjective_unramified_of_isIntegralClosure K L b
  refine ⟨Additive.ofMul c, ?_⟩
  erw [Rep.norm_apply, Representation.norm, LinearMap.sum_apply]
  apply Additive.toMul.injective
  let f (σ : Gal(L/K)) : Additive 𝒪[L]ˣ :=
    A.ρ σ (show A from Additive.ofMul (α := 𝒪[L]ˣ) c)
  change Additive.toMul (∑ σ, f σ) = (show Additive 𝒪[L]ˣ from a.val).toMul
  rw [toMul_sum]
  change tateNorm Gal(L/K) 𝒪[L]ˣ c = (show Additive 𝒪[L]ˣ from a.val).toMul
  exact (LocalFieldTheory.integerUnitsMap_normIntegerUnits_eq_prod_gal K L c).symm.trans
    ((congrArg (integerUnitsMapOfValuationExtension K L) hc).trans hb)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsUniformAddGroup L]
  [FiniteDimensional K L] [IsGalois K L] [Module.Finite 𝒪[K] 𝒪[L]]
  [IsUnramifiedValuedExtension K L] in
private theorem ordinaryIntegralTwoValues_mem_range
    (z : ContinuousCohomology.cocycles (galoisUnitsRep K L) 2)
    (hz : ∀ g h k : Gal(L/K),
      valuationMap L
        (((TopRep.homogeneousCochains (galoisUnitsRep K L)).iCycles 2 z).val g h k) = 0)
    (p : Gal(L/K) × Gal(L/K)) :
    ∃ a : integerUnitsRep K L, integerUnitCoefficientMap K L a =
      ContinuousCohomology.dehomogenizeIntegralTwo (galoisUnitsRep K L) z p := by
  let B := liftedGaloisUnitsRep K L
  let X := galoisUnitsRep K L
  let c : groupCohomology.cocycles₂ B := ContinuousCohomology.dehomogenizeIntegralTwo X z
  have hx : valuationMap L (c p) = 0 :=
    (congrArg (valuationMap L)
      (ContinuousCohomology.dehomogenizeIntegralTwo_apply X z p.1 p.2)).trans
      (hz 1 p.1 (p.1 * p.2))
  obtain ⟨a, ha⟩ := (integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero L
    (show Additive Lˣ from c p).toMul).mpr hx
  have h := (integerUnitCoefficientMap_apply K L (Additive.ofMul a)).trans
    (congrArg Additive.ofMul ha)
  exact ⟨Additive.ofMul a, h⟩

/-- An actual continuous relative Brauer cocycle with integral-unit values
represents zero in an unramified finite extension. -/
theorem unramifiedCocycle_class_eq_zero_of_units
    (z : ContinuousCohomology.cocycles (galoisUnitsRep K L) 2)
    (hz : ∀ g h k : Gal(L/K),
      valuationMap L
        (((TopRep.homogeneousCochains (galoisUnitsRep K L)).iCycles 2 z).val g h k) = 0) :
    ContinuousCohomology.π (galoisUnitsRep K L) 2 z = 0 := by
  let B := liftedGaloisUnitsRep K L
  let c : groupCohomology.cocycles₂ B :=
    ContinuousCohomology.dehomogenizeIntegralTwo (galoisUnitsRep K L) z
  have hι : Function.Injective (fun a : integerUnitsRep K L => integerUnitCoefficientMap K L a) :=
    integerUnitsToFieldUnits_injective L
  have h := ordinaryH2_eq_zero_of_values_in_range (integerUnitCoefficientMap K L) hι c
    (ordinaryIntegralTwoValues_mem_range K L z hz) (integerUnitsH2_eq_zero K L)
  exact (ContinuousCohomology.dehomogenizeIntegralTwo_class_eq_zero_iff (galoisUnitsRep K L) z).mp h

end ClassFieldTheory.Brauer

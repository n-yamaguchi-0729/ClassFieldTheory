/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.CyclicNorm
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTateNakayama
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTateNorm
public import Nyll.GaloisCohomology.Cyclic.IntegralTateCyclicCupEvaluation

/-! # The signed bar representative in cyclic local reciprocity -/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Module
open ClassFieldTower.Cohomology LocalFieldTheory
open IntegralGroupCohomology.Universe
open scoped ValuativeRel

namespace ClassFieldTheory.Brauer

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L] (i : L →ₐ[K] SeparableClosure K)

local notation "U" => Rep.ofAlgebraAutOnUnits K L
local notation "J" => localLiftedGaloisGroup K L
local notation "V" => localLiftedUnitsRepresentation K L
local notation "E" => fundamentalClassStage K L i

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The chosen embedding carries the same cyclic generator to the finite stage. -/
theorem localEmbeddedGenerator (g : Gal(L/K)) (hg : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers g) :
    ∀ q : Gal(E/K), q ∈ Subgroup.zpowers (localLiftedStageGroupEquiv K L i (ULift.up g)) := by
  intro q
  let e := localLiftedStageGroupEquiv K L i
  obtain ⟨x, rfl⟩ := e.surjective q
  obtain ⟨n, hn⟩ := ulift_generator g hg x
  exact ⟨n, (map_zpow e (ULift.up g) n).symm.trans (congrArg e hn)⟩

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem localCommonCarryReindex (g : Gal(L/K))
    (hg : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers g) (a : Kˣ) :
    let e := localLiftedStageGroupEquiv K L i
    let f := localLiftedStageUnitsEquiv K L i
    let h := e (ULift.up g)
    let hh := localEmbeddedGenerator K L i g hg
    let : IsCyclic Gal(E/K) := CyclicCohomology.isCyclic_of_generator h hh
    let : CommGroup Gal(E/K) := IsCyclic.commGroup
    let b := universeLiftFixedVector U (CyclicCohomology.baseUnitToInvariantUnit K L a)
    groupCohomology.reindexTwoCocycle
        (A := (IntegralGroupCohomology.coefficientFunctor J).obj V)
        (B := liftedGaloisUnitsRep K E) e f (localLiftedStageUnitsEquiv_comm K L i)
        (commonCarryCocycle V (ULift.up g) (ulift_generator g hg) b) =
      finiteCyclicCarryTwoCocycle (liftedGaloisUnitsRep K E) h hh
        (liftedBaseUnitCycle K E h a) := by
  intro e f h hh hcyc hcomm b
  apply groupCohomology.cocycles₂_ext
  intro x y
  have he : (finiteCyclicCarry (ULift.up g) (ulift_generator g hg) (e.symm x) (e.symm y)) =
      finiteCyclicCarry h hh x y := by
    have ht := finiteCyclicCarry_equiv e (ULift.up g) (ulift_generator g hg) hh
      (e.symm x) (e.symm y)
    rw [e.apply_symm_apply, e.apply_symm_apply] at ht
    exact ht
  change f (finiteCyclicCarry (ULift.up g) (ulift_generator g hg) (e.symm x) (e.symm y) • b.val) =
    finiteCyclicCarry h hh x y • (liftedBaseUnitCycle K E h a).val
  rw [he, map_nsmul]
  apply congrArg (fun z : liftedGaloisUnitsRep K E => finiteCyclicCarry h hh x y • z)
  apply Additive.toMul.injective
  apply Units.ext
  exact i.equivFieldRange.commutes (a : K)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The Tate carry with the original base unit is the identical relative
cyclic class on the finite embedded stage. -/
theorem localLiftedTateH2EmbeddedEquiv_carry (g : Gal(L/K))
    (hg : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers g) (a : Kˣ) :
    let h := localLiftedStageGroupEquiv K L i (ULift.up g)
    let hh := localEmbeddedGenerator K L i g hg
    let : IsCyclic Gal(E/K) := CyclicCohomology.isCyclic_of_generator h hh
    localLiftedTateH2EmbeddedEquiv K L i
        (tateCyclicCarryClass V (ULift.up g) (ulift_generator g hg)
          (universeLiftFixedVector U (CyclicCohomology.baseUnitToInvariantUnit K L a))) =
      cyclicContinuousUnitClass K E h hh (Additive.ofMul a) := by
  intro h hh hcyc
  let e := localLiftedStageGroupEquiv K L i
  let f := localLiftedStageUnitsEquiv K L i
  let hf := localLiftedStageUnitsEquiv_comm K L i
  let c := continuousRelativeUnitsH2Equiv K E
  let b := universeLiftFixedVector U (CyclicCohomology.baseUnitToInvariantUnit K L a)
  let d := groupCohomology.equivariantH2AddEquiv
    (A := (IntegralGroupCohomology.coefficientFunctor J).obj V) (B := liftedGaloisUnitsRep K E)
    e f hf
  let z := commonCarryCocycle V (ULift.up g) (ulift_generator g hg) b
  have hTate := tatePositiveIsoCommonCohomology_hom_cyclicCarry V (ULift.up g)
    (ulift_generator g hg) b
  have hStage := groupCohomology.equivariantH2AddEquiv_H2π e f hf z
  have hCarry := congrArg (groupCohomology.H2π (liftedGaloisUnitsRep K E))
    (localCommonCarryReindex K L i g hg a)
  exact congrArg c.symm ((congrArg d hTate).trans (hStage.trans hCarry))

/-- If the cyclic class of a unit has the defining fundamental invariant,
the negative bar generator maps to the original fixed unit class. -/
theorem localTateNakayama_neg_bar_of_cyclicInvariant (g : Gal(L/K))
    (hg : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers g) (a : Kˣ)
    (ha : let h := localLiftedStageGroupEquiv K L i (ULift.up g)
      let hh := localEmbeddedGenerator K L i g hg
      let : IsCyclic Gal(E/K) := CyclicCohomology.isCyclic_of_generator h hh
      localBrauerInvariant K (cyclicBrauerClass E h hh a) =
        (((1 : ℚ) / (finrank K E : ℕ) : ℚ) : AddCircle (1 : ℚ))) :
    localTateNakayama K L i (-2) (-(tateNegTwoUnitClass Gal(L/K) g)) =
      fixedClass U (CyclicCohomology.baseUnitToInvariantUnit K L a) := by
  let h := localLiftedStageGroupEquiv K L i (ULift.up g)
  let hh := localEmbeddedGenerator K L i g hg
  let : IsCyclic Gal(E/K) := CyclicCohomology.isCyclic_of_generator h hh
  let e := localLiftedTateH2EmbeddedEquiv K L i
  have hc : cyclicContinuousUnitClass K E h hh (Additive.ofMul a) = localFundamentalClass K E := by
    apply (localBrauerInvariantEquiv K).injective.comp (finiteInflation_injective E)
    change localBrauerInvariant K (cyclicBrauerClass E h hh a) =
      relativeLocalBrauerInvariant K E (localFundamentalClass K E)
    exact ha.trans (relativeLocalBrauerInvariant_fundamentalClass K E).symm
  have ht : localFundamentalTateClass K L i =
      tateCyclicCarryViaLift U g hg (CyclicCohomology.baseUnitToInvariantUnit K L a) := by
    apply (tateIsoCommon V 2).symm.toLinearEquiv.injective
    apply e.injective
    change e ((tateIsoCommon V 2).inv (localFundamentalTateClass K L i)) =
      e ((tateIsoCommon V 2).inv
        (tateCyclicCarryViaLift U g hg (CyclicCohomology.baseUnitToInvariantUnit K L a)))
    rw [localFundamentalTateClass_lift]
    unfold tateCyclicCarryViaLift
    rw [Iso.hom_inv_id_apply, localLiftedTateH2EmbeddedEquiv_carry K L i g hg a]
    exact hc.symm
  rw [map_neg, localTateNakayama_apply, ht]
  have hcup := tateCupTrivialInteger_negTwo_bar_carry U g hg
    (CyclicCohomology.baseUnitToInvariantUnit K L a)
  exact (congrArg Neg.neg hcup).trans (neg_neg _)

end ClassFieldTheory.Brauer

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.EmbeddedInflation
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.RestrictionDegree
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTateCyclicCup

/-! # The literal restricted fundamental class in the cyclic carry calculation -/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory ContinuousCohomology ClassFieldTower.Cohomology LocalFieldTheory
open IntegralGroupCohomology.Universe
open scoped ValuativeRel

namespace ClassFieldTheory.Brauer

private theorem tateH2_reindex_restrict
    {G : Type v} [Group G] [Fintype G] (A : Rep.{v} ℤ G)
    (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]
    {G₀ G₁ : Type u} [Group G₀] [Group G₁]
    {B₀ : Rep.{u} (ULift.{u} ℤ) G₀} {B₁ : Rep.{u} (ULift.{u} ℤ) G₁}
    (e₀ : G ≃* G₀) (e₁ : H ≃* G₁)
    (f₀ : (IntegralGroupCohomology.coefficientFunctor G).obj A ≃+ B₀)
    (f₁ : (IntegralGroupCohomology.coefficientFunctor H).obj (Rep.res H.subtype A) ≃+ B₁)
    (hf₀ : ∀ g a, f₀ (((IntegralGroupCohomology.coefficientFunctor G).obj A).ρ g a) =
      B₀.ρ (e₀ g) (f₀ a))
    (hf₁ : ∀ g a, f₁ (((IntegralGroupCohomology.coefficientFunctor H).obj
      (Rep.res H.subtype A)).ρ g a) = B₁.ρ (e₁ g) (f₁ a))
    (r : G₁ →* G₀) (k : Rep.res r B₀ ⟶ B₁)
    (he : ∀ g : H, e₀ g.val = r (e₁ g))
    (hk : ∀ a : (IntegralGroupCohomology.coefficientFunctor G).obj A, f₁ a = k (f₀ a))
    (z : tate A 2) :
    groupCohomology.equivariantH2AddEquiv e₁ f₁ hf₁
      ((tatePositiveIsoCommonCohomology (Rep.res H.subtype A) 2).hom (tateRestrict H A 2 z)) =
    groupCohomology.map r k 2
      (groupCohomology.equivariantH2AddEquiv e₀ f₀ hf₀
        ((tatePositiveIsoCommonCohomology A 2).hom z)) := by
  let T := (IntegralGroupCohomology.coefficientFunctor H).obj (Rep.res H.subtype A)
  let z₀ : groupCohomology.H2 ((IntegralGroupCohomology.coefficientFunctor G).obj A) :=
    (tatePositiveIsoCommonCohomology A 2).hom z
  have hmap : (tatePositiveIsoCommonCohomology (Rep.res H.subtype A) 2).hom
      (tateRestrict H A 2 z) = groupCohomology.map H.subtype (𝟙 T) 2 z₀ :=
    tateRestrict_positive_comp_common H 2 A z
  let q := groupCohomology.equivariantH2AddEquiv e₁ f₁ hf₁
  exact (congrArg (q : groupCohomology.H2 T → _) hmap).trans
    (groupCohomology.equivariantH2AddEquiv_map e₀ f₀ hf₀ e₁ f₁ hf₁
      H.subtype r (𝟙 T) k he hk z₀)

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [IsGalois K L] (i : L →ₐ[K] SeparableClosure K)

local notation "J" => localLiftedGaloisGroup K L
local notation "V" => localLiftedUnitsRepresentation K L
local notation "E" => fundamentalClassStage K L i

variable (H : Subgroup (localLiftedGaloisGroup K L)) [Fintype H]
  (F : Type u) [Field F] [Algebra K F]
  (D : FiniteGaloisIntermediateField F (SeparableClosure F)) [Algebra K D] [IsScalarTower K F D]

/-- The lifted unit representation restricted to the original subgroup. -/
abbrev localLiftedSubgroupUnitsRepresentation
    (U : Subgroup (localLiftedGaloisGroup K L)) : Rep.{v} ℤ U := by
  let J₀ := localLiftedGaloisGroup K L
  let A : Rep.{v} ℤ J₀ := localLiftedUnitsRepresentation K L
  let r : U →* J₀ := U.subtype
  exact Rep.res (k := ℤ) (G := J₀) (H := U) r A

local notation "W" => localLiftedSubgroupUnitsRepresentation K L H
local notation "R" => CategoryTheory.Functor.obj (IntegralGroupCohomology.coefficientFunctor H) W

variable (e : H ≃* Gal(D/F))
  (l : (IntegralGroupCohomology.coefficientFunctor H).obj
    (localLiftedSubgroupUnitsRepresentation K L H) ≃+ liftedGaloisUnitsRep F D)
  (hl : ∀ g a, l (((IntegralGroupCohomology.coefficientFunctor H).obj
    (localLiftedSubgroupUnitsRepresentation K L H)).ρ g a) =
      (liftedGaloisUnitsRep F D).ρ (e g) (l a))

/-- The original subgroup degree-two classes under an actual group and unit equivalence. -/
def localLiftedSubgroupTateH2Equiv : tate W 2 ≃+ relativeBr D :=
  ((tatePositiveIsoCommonCohomology W 2).toLinearEquiv.toAddEquiv).trans
    ((groupCohomology.equivariantH2AddEquiv (A := R) (B := liftedGaloisUnitsRep F D) e l hl).trans
      (continuousRelativeUnitsH2Equiv F D).symm)

section Restriction

variable [Fintype (localLiftedGaloisGroup K L ⧸ H)]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- This comparison intertwines actual finite-group restriction with actual
relative restriction on the embedded unit cohomology. -/
theorem localLiftedSubgroupTateH2Equiv_restriction (j : E →ₐ[K] D)
    (he : ∀ h : H, localLiftedStageGroupEquiv K L i h.val =
      embeddedGaloisRestriction (B := F) j (e h))
    (hc : ∀ a : V, l a = (Units.map j.toMonoidHom).toAdditive (localLiftedStageUnitsEquiv K L i a))
    (z : tate V 2) :
    localLiftedSubgroupTateH2Equiv K L H F D e l hl (tateRestrict H V 2 z) =
      embeddedRelativeRestriction E j (localLiftedTateH2EmbeddedEquiv K L i z) := by
  let r := embeddedGaloisRestriction (B := F) j
  let hr := embeddedGaloisRestriction_commutes (B := F) j
  let f := localLiftedStageUnitsEquiv K L i
  let h := localLiftedStageUnitsEquiv_comm K L i
  let p := localLiftedStageGroupEquiv K L i
  let B := (IntegralGroupCohomology.coefficientFunctor J).obj V
  let p₀ := groupCohomology.equivariantH2AddEquiv (A := B) (B := liftedGaloisUnitsRep K E) p f h
  let p₁ := groupCohomology.equivariantH2AddEquiv (A := R) (B := liftedGaloisUnitsRep F D) e l hl
  let c₀ := continuousRelativeUnitsH2Equiv K E
  let c₁ := continuousRelativeUnitsH2Equiv F D
  let φ := liftedGaloisUnitsMap r j.toRingHom hr
  apply c₁.injective
  change c₁ (c₁.symm (p₁ ((tatePositiveIsoCommonCohomology W 2).hom (tateRestrict H V 2 z)))) =
    c₁ ((ContinuousCohomology.map r (galoisUnitsMap r j.toRingHom hr) 2)
      (c₀.symm (p₀ ((tatePositiveIsoCommonCohomology V 2).hom z))))
  rw [c₁.apply_symm_apply, continuousRelativeUnitsH2Equiv_map, c₀.apply_symm_apply]
  exact tateH2_reindex_restrict V H p e f l h hl r.toMonoidHom φ he
    (fun a => (hc a).trans (liftedGaloisUnitsMap_apply r j.toRingHom hr (f a)).symm) z

end Restriction

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FiniteDimensional K L]
  [IsGalois K L] [Algebra K F] [Algebra K ↥D.toIntermediateField]
  [IsScalarTower K F ↥D.toIntermediateField] in
private theorem localSubgroupCarryReindex
    (g : H) (hg : ∀ x : H, x ∈ Subgroup.zpowers g)
    (hg' : ∀ x : Gal(D/F), x ∈ Subgroup.zpowers (e g))
    [IsCyclic Gal(D/F)] (a : (W).ρ.invariants) (b : Fˣ)
    (hab : l a.val = (liftedBaseUnitCycle F D (e g) b).val) :
    let : CommGroup Gal(D/F) := IsCyclic.commGroup
    groupCohomology.reindexTwoCocycle (A := R) (B := liftedGaloisUnitsRep F D) e l hl
        (commonCarryCocycle W g hg a) =
      finiteCyclicCarryTwoCocycle (liftedGaloisUnitsRep F D) (e g) hg'
        (liftedBaseUnitCycle F D (e g) b) := by
  intro hgroup
  apply groupCohomology.cocycles₂_ext
  intro x y
  have hxy := finiteCyclicCarry_equiv e g hg hg' (e.symm x) (e.symm y)
  rw [e.apply_symm_apply, e.apply_symm_apply] at hxy
  let M := (IntegralGroupCohomology.coefficientFunctor H).obj
    (localLiftedSubgroupUnitsRepresentation K L H)
  let a₀ : M := a.val
  let b₀ : liftedGaloisUnitsRep F D := (liftedBaseUnitCycle F D (e g) b).val
  change l (finiteCyclicCarry g hg (e.symm x) (e.symm y) • a₀) =
    finiteCyclicCarry (e g) hg' x y • b₀
  rw [hxy]
  exact (map_nsmul l _ a₀).trans (congrArg (_ • ·) hab)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FiniteDimensional K L]
  [IsGalois K L] [Algebra K F] [Algebra K ↥D.toIntermediateField]
  [IsScalarTower K F ↥D.toIntermediateField] in
/-- A carry on a cyclic subgroup has the same representative on the embedded stage. -/
theorem localLiftedSubgroupTateH2Equiv_carry (g : H) (hg : ∀ x : H, x ∈ Subgroup.zpowers g)
    (hg' : ∀ x : Gal(D/F), x ∈ Subgroup.zpowers (e g))
    [IsCyclic Gal(D/F)] (a : (W).ρ.invariants) (b : Fˣ)
    (hab : l a.val = (liftedBaseUnitCycle F D (e g) b).val) :
    localLiftedSubgroupTateH2Equiv K L H F D e l hl (tateCyclicCarryClass W g hg a) =
      cyclicContinuousUnitClass F D (e g) hg' (Additive.ofMul b) := by
  let c := continuousRelativeUnitsH2Equiv F D
  let p := groupCohomology.equivariantH2AddEquiv (A := R) (B := liftedGaloisUnitsRep F D) e l hl
  let z := commonCarryCocycle W g hg a
  have hTate := tatePositiveIsoCommonCohomology_hom_cyclicCarry W g hg a
  have hStage := groupCohomology.equivariantH2AddEquiv_H2π e l hl z
  have hCarry := congrArg (groupCohomology.H2π (liftedGaloisUnitsRep F D))
    (localSubgroupCarryReindex K L H F D e l hl g hg hg' a b hab)
  exact congrArg c.symm ((congrArg p hTate).trans (hStage.trans hCarry))

section FundamentalRestriction

open Module

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [FiniteDimensional k F] [Algebra.IsSeparable k F]
  [Valuation.HasExtension (ValuativeRel.valuation k) (ValuativeRel.valuation F)]
  (M : FiniteGaloisIntermediateField k (SeparableClosure k))
  (D₀ : FiniteGaloisIntermediateField F (SeparableClosure F))
  [Algebra k D₀] [IsScalarTower k F D₀]

/-- Relative restriction sends the local fundamental class to the upper
fundamental class when the degrees agree with the given tower. -/
theorem embeddedRelativeRestriction_localFundamentalClass
    (j : M →ₐ[k] D₀) (hdegree : finrank k M = finrank k F * finrank F D₀) :
    embeddedRelativeRestriction (A := F) M j (localFundamentalClass k M) =
      localFundamentalClass F D₀ := by
  apply (localBrauerInvariantEquiv F).injective.comp (finiteInflation_injective D₀)
  change localBrauerInvariant F (finiteInflation D₀
      (embeddedRelativeRestriction (A := F) M j (localFundamentalClass k M))) =
    relativeLocalBrauerInvariant F D₀ (localFundamentalClass F D₀)
  rw [← restrict_finiteInflation_eq_finiteInflation_embeddedRelativeRestriction M D₀ j,
    localBrauerInvariant_restrict]
  change finrank k F • relativeLocalBrauerInvariant k M (localFundamentalClass k M) = _
  rw [relativeLocalBrauerInvariant_fundamentalClass, relativeLocalBrauerInvariant_fundamentalClass,
    ← AddCircle.coe_nsmul, nsmul_eq_mul]
  apply congrArg (fun z : ℚ => (z : AddCircle (1 : ℚ)))
  have hm : (finrank k F : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [hdegree, Nat.cast_mul, mul_one_div]
  simpa only [mul_one] using mul_div_mul_left (1 : ℚ) (finrank F D₀ : ℚ) hm

end FundamentalRestriction

end ClassFieldTheory.Brauer

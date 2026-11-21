/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.IntegralUnitClass
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalInvariant
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm
public import Nyll.GaloisCohomology.Topology.ContinuousCorestriction
public import Nyll.GaloisCohomology.Topology.DiscreteOriginalH2Naturality

/-! # Actual corestriction over a finite embedded local extension -/

@[expose] public section

open scoped ValuativeRel BigOperators
open CategoryTheory TopRep ContinuousCohomology ClassFormation CyclicCohomology
open LocalClassFieldTheory LocalFieldTheory RamificationTheory

noncomputable section
namespace ClassFieldTheory.Brauer

universe u

/-- The unit class of an integer class pulled back along a continuous group map. -/
def unitsIntegralClassAfterRestriction
    {F G : Type u} [Field F] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (r : Gal(SeparableClosure F/F) →ₜ* G) (b : Fˣ) :
    continuousCohomology 2 (trivialIntegralTopRep G) →+ Br F :=
  (map r (integralRestrictionCoefficient r ≫ unitScalarCoefficientMap F b) 2).hom.toLinearMap
    |>.toAddMonoidHom

/-- The composed coefficient map first restricts the integer class and then
multiplies it by the upper-field unit. -/
theorem unitsIntegralClassAfterRestriction_apply
    {F G : Type u} [Field F] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (r : Gal(SeparableClosure F/F) →ₜ* G) (b : Fˣ)
    (x : continuousCohomology 2 (trivialIntegralTopRep G)) :
    unitsIntegralClassAfterRestriction r b x =
      unitsIntegralClass F b (integralRestriction r x) := by
  let J := Gal(SeparableClosure F/F)
  let i := ContinuousMonoidHom.id J
  let f := integralRestrictionCoefficient r
  let g := unitScalarCoefficientMap F b
  exact (map_comp_eq_apply r i r f g (f ≫ g) (fun _ => rfl)
    (fun a => (ConcreteCategory.comp_apply f g a).symm) 2 x).symm

private theorem map_through_restriction
    {G J H : Type u} [Group G] [Group J] [Group H]
    [TopologicalSpace G] [TopologicalSpace J] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup J] [IsTopologicalGroup H]
    {X : TopRep.{u} ℤ G} {Y : TopRep.{u} ℤ J} {Z : TopRep.{u} ℤ H}
    (r : J →ₜ* G) (s : H →ₜ* J) (i : H →ₜ* G)
    (f : TopRep.res r.toMonoidHom X ⟶ Y) (g : TopRep.res s.toMonoidHom Y ⟶ Z)
    (h : TopRep.res i.toMonoidHom X ⟶ Z)
    (hGroups : ∀ σ, r (s σ) = i σ) (hCoeffs : ∀ a : X, g (f a) = h a)
    (x : continuousCohomology 2 X) :
    map s g 2 (map r f 2 x) =
      map (ContinuousMonoidHom.id H) h 2 (map i (𝟙 (TopRep.res i.toMonoidHom X)) 2 x) :=
  (map_comp_eq_apply r s i f g h hGroups hCoeffs 2 x).trans
    (map_comp_eq_apply i (ContinuousMonoidHom.id H) i
      (𝟙 (TopRep.res i.toMonoidHom X)) h h (fun _ => rfl) (fun _ => rfl) 2 x).symm

attribute [local instance] stageSeparableClosureAlgebra

variable (K : Type u) [Field K]
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    (j : SeparableClosure K ≃ₐ[E] SeparableClosure E)

/-- The actual open Galois subgroup fixing the embedded finite extension. -/
def stageOpenFixingSubgroup : OpenSubgroup Gal(SeparableClosure K/K) where
  toSubgroup := E.fixingSubgroup
  isOpen' := (InfiniteGalois.isOpen_iff_finite (K := SeparableClosure K) E).mpr inferInstance

local notation "H" => stageOpenFixingSubgroup K E
local notation "Q" => Gal(SeparableClosure K/K) ⧸ (H : Subgroup Gal(SeparableClosure K/K))
local notation "Gₖ" => Gal(SeparableClosure K/K)
local notation "Gₑ" => Gal(SeparableClosure E/E)
local notation "Zₖ" => trivialIntegralTopRep Gₖ
local notation "Zₑ" => trivialIntegralTopRep Gₑ

/-- The original continuous restriction on integer coefficients for the chosen embeddings. -/
def embeddedIntegralRestriction : continuousCohomology 2 Zₖ →+ continuousCohomology 2 Zₑ :=
  integralRestriction (embeddedAbsoluteRestrictionHom K E j)

/-- The chosen closure comparison identifies the upper absolute Galois
group with its actual open fixing subgroup. -/
def embeddedAbsoluteRestrictionEquiv :
    Gₑ ≃ₜ* ↥(stageOpenFixingSubgroup K E).toSubgroup := by
  let e : Gal(SeparableClosure E/E) ≃* ↥(stageOpenFixingSubgroup K E).toSubgroup :=
    (AlgEquiv.autCongr j.symm).trans E.fixingSubgroupEquiv.symm
  have hcont : Continuous e := by
    change Continuous (fun σ : Gal(SeparableClosure E/E) =>
      (⟨embeddedAbsoluteRestrictionHom K E j σ, (e σ).property⟩ :
        ↥(stageOpenFixingSubgroup K E).toSubgroup))
    exact (embeddedAbsoluteRestrictionHom K E j).continuous.subtype_mk fun σ => (e σ).property
  exact { e with
    continuous_toFun := hcont
    continuous_invFun := hcont.continuous_symm_of_equiv_compact_to_t2 }

theorem embeddedAbsoluteRestrictionEquiv_coe (σ : Gal(SeparableClosure E/E)) :
    (embeddedAbsoluteRestrictionEquiv K E j σ : Gal(SeparableClosure K/K)) =
      embeddedAbsoluteRestrictionHom K E j σ := rfl

/-- The upper unit coefficients transported to the actual open fixing subgroup. -/
def embeddedUnitsTransport :
    TopRep.res (embeddedAbsoluteRestrictionEquiv K E j).symm.toMonoidHom (unitsRep E) ⟶
      TopRep.res (H).toSubgroup.subtype (unitsRep K) := by
  let jInv : SeparableClosure E ≃ₐ[E] SeparableClosure K := j.symm
  let f : Additive (SeparableClosure E)ˣ →ₗ[ℤ] Additive (SeparableClosure K)ˣ :=
    (Units.map jInv.toRingEquiv.toMonoidHom).toAdditive.toIntLinearMap
  refine TopRep.ofHom {
    toLinearMap := f
    cont := continuous_of_discreteTopology
    isIntertwining' := fun σ => by
      apply ContinuousLinearMap.ext
      intro a
      apply Units.ext
      apply j.injective
      let e := embeddedAbsoluteRestrictionEquiv K E j
      let x : SeparableClosure E := ((show Additive (SeparableClosure E)ˣ from a).toMul :
        (SeparableClosure E)ˣ)
      have hσ : embeddedAbsoluteRestrictionHom K E j (e.symm σ) = (σ : Gₖ) :=
        (embeddedAbsoluteRestrictionEquiv_coe K E j (e.symm σ)).symm.trans
          (congrArg Subtype.val (e.apply_symm_apply σ))
      have h := embeddedAbsoluteRestrictionHom_commutes K E j (e.symm σ) (j.symm x)
      rw [hσ, j.apply_symm_apply] at h
      change j (j.symm (e.symm σ x)) = j ((σ : Gal(SeparableClosure K/K)) (j.symm x))
      rw [j.apply_symm_apply]
      exact h.symm }

/-- The inverse closure identification as a continuous group homomorphism. -/
def embeddedAbsoluteRestrictionInverseHom :
    ↥(stageOpenFixingSubgroup K E).toSubgroup →ₜ* Gₑ :=
  ⟨(embeddedAbsoluteRestrictionEquiv K E j).symm.toMonoidHom,
    (embeddedAbsoluteRestrictionEquiv K E j).symm.continuous_toFun⟩

/-- Transport upper absolute Brauer classes to field units on the open fixing subgroup. -/
def embeddedUnitsCohomologyTransport :
    Br E →+ continuousCohomology 2 (TopRep.res (H).toSubgroup.subtype (unitsRep K)) := by
  let f := ContinuousCohomology.map
    (X := unitsRep E) (Y := TopRep.res (H).toSubgroup.subtype (unitsRep K))
    (embeddedAbsoluteRestrictionInverseHom K E j) (embeddedUnitsTransport K E j) 2
  exact f.hom.toLinearMap.toAddMonoidHom

/-- Actual degree-two corestriction uses the upper field's genuine unit
action transported to the fixing subgroup, followed by the finite coset sum. -/
def embeddedAbsoluteBrCorestriction : Br E →+ Br K :=
  (ContinuousCohomology.corestrict (unitsRep K) H 2).comp (embeddedUnitsCohomologyTransport K E j)

private theorem embeddedUnitsTransport_restrict (x : Br K) :
    embeddedUnitsCohomologyTransport K E j (embeddedAbsoluteBrRestriction K E j x) =
      openRestriction (unitsRep K) H 2 x := by
  let X := unitsRep K
  let Y := TopRep.res (H).toSubgroup.subtype X
  let e := embeddedAbsoluteRestrictionEquiv K E j
  let r := embeddedAbsoluteRestrictionHom K E j
  let ι : ↥(stageOpenFixingSubgroup K E).toSubgroup →ₜ* Gₖ :=
    ProCGroups.ContinuousMonoidHom.subtype (H).toSubgroup
  let s := embeddedAbsoluteRestrictionInverseHom K E j
  let φ := galoisUnitsMap r j.toRingEquiv.toRingHom (embeddedAbsoluteRestrictionHom_commutes K E j)
  let ψ := embeddedUnitsTransport K E j
  have hr (σ : ↥(stageOpenFixingSubgroup K E).toSubgroup) : r (s σ) = ι σ := by
    exact (embeddedAbsoluteRestrictionEquiv_coe K E j (s σ)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply σ))
  have hψ (a : X) : ψ (φ a) = a := by
    apply Units.ext
    let a' : Additive (SeparableClosure K)ˣ := a
    exact j.symm_apply_apply (a'.toMul : SeparableClosure K)
  exact map_comp_eq_apply (X := X) (Y := unitsRep E) (Z := Y)
    r s ι φ ψ (𝟙 Y) hr hψ 2 x


/-- The actual composite of corestriction and restriction is multiplication
by the finite field degree. -/
theorem embeddedAbsoluteBrCorestriction_restriction (x : Br K) :
    embeddedAbsoluteBrCorestriction K E j (embeddedAbsoluteBrRestriction K E j x) =
      Module.finrank K E • x := by
  change corestrict (unitsRep K) H 2
    (embeddedUnitsCohomologyTransport K E j (embeddedAbsoluteBrRestriction K E j x)) = _
  rw [embeddedUnitsTransport_restrict K E j, corestrict_openRestriction_two]
  congr 1
  exact (IntermediateField.finrank_eq_fixingSubgroup_index (F := K) (SeparableClosure K) E).symm

private def embeddedUnitInvariant (b : Eˣ) :
    (TopRep.res (H).toSubgroup.subtype (unitsRep K)).invariants :=
  ⟨Additive.ofMul (Units.map (algebraMap E (SeparableClosure K)).toMonoidHom b), fun σ => by
    apply Additive.toMul.injective
    apply Units.ext
    exact (IntermediateField.mem_fixingSubgroup_iff E (σ : Gₖ)).mp σ.property
      (b : E) (b : E).property⟩

private def embeddedFixingCosetEquivAlgHom : Q ≃ (E →ₐ[K] SeparableClosure K) := by
  let Ω := SeparableClosure K
  let B := closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)
  let D := closedFixingSubgroup K Ω E
  let h := fixingSubgroupLeBase K Ω E
  let e : Gₖ ≃ B.toSubgroup :=
    { toFun := fun σ => ⟨σ, by
        change σ ∈ (⊥ : IntermediateField K Ω).fixingSubgroup
        rw [IntermediateField.fixingSubgroup_bot]
        exact Subgroup.mem_top σ⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => Subtype.ext rfl }
  let : Algebra.IsSeparable K E := Algebra.isSeparable_tower_bot_of_isSeparable K E Ω
  let eQ : Q ≃ (B.toSubgroup ⧸ extensionSubgroup B D h) :=
    Quotient.congr e (fun _ _ => by simp only [QuotientGroup.leftRel_apply]; rfl)
  exact eQ.trans (baseFixingCosetEquivAlgHom K Ω E)

private theorem embeddedFixingCosetEquivAlgHom_mk (σ : Gₖ) :
    embeddedFixingCosetEquivAlgHom K E (QuotientGroup.mk σ) =
      σ.toAlgHom.comp E.val := rfl

private theorem embeddedUnitInvariant_norm (b : Eˣ) :
    openSubgroupNorm (unitsRep K) H (embeddedUnitInvariant K E b) =
      baseUnitInvariant K (normUnits K E b) := by
  let Ω := SeparableClosure K
  let : Algebra.IsSeparable K E := Algebra.isSeparable_tower_bot_of_isSeparable K E Ω
  let : Fintype Q := openSubgroupQuotientFintype H
  let : Fintype (E →ₐ[K] Ω) := PowerBasis.AlgHom.fintype (Field.powerBasisOfFiniteOfSeparable K E)
  let r : Q → Gₖ := Quotient.out
  have hr (q : Q) : QuotientGroup.mk (r q) = q := Quotient.out_eq q
  apply Subtype.ext
  rw [openSubgroupNorm_val (unitsRep K) H (embeddedUnitInvariant K E b) r hr]
  apply Additive.toMul.injective
  apply Units.ext
  change (Units.coeHom Ω)
      (∏ q : Q, Additive.toMul ((unitsRep K).ρ (r q) (embeddedUnitInvariant K E b))) =
    algebraMap K Ω (Algebra.norm K (b : E))
  rw [map_prod]
  calc
    _ = ∏ σ : E →ₐ[K] Ω, σ (b : E) := by
      refine Fintype.prod_equiv (embeddedFixingCosetEquivAlgHom K E) _ _ (fun q => ?_)
      have hq : (embeddedFixingCosetEquivAlgHom K E q) (b : E) =
          (embeddedFixingCosetEquivAlgHom K E (QuotientGroup.mk (r q))) (b : E) :=
        congrArg (fun t : Q => (embeddedFixingCosetEquivAlgHom K E t) (b : E)) (hr q).symm
      rw [embeddedFixingCosetEquivAlgHom_mk K E] at hq
      exact hq.symm
    _ = _ := (algebraMap_norm_eq_prod_embeddings_of_isSepClosed K Ω E (b : E)).symm

/-- Restrict an integer class and multiply it by an actual upper-field unit. -/
abbrev embeddedUnitsIntegralClass (b : Eˣ) :=
  unitsIntegralClassAfterRestriction (embeddedAbsoluteRestrictionHom K E j) b

private abbrev embeddedInvariantCoefficientMap (b : Eˣ) :
    TopRep.res (H).toSubgroup.subtype Zₖ ⟶ TopRep.res (H).toSubgroup.subtype (unitsRep K) :=
  rightInvariantCoefficientMap
    (A := TopRep.res (H).toSubgroup.subtype Zₖ)
    (B := TopRep.res (H).toSubgroup.subtype (unitsRep K))
    (C := TopRep.res (H).toSubgroup.subtype (unitsRep K))
    (unitScalarPairing K) (unitScalarPairing_continuous K)
    (fun h => unitScalarPairing_equivariant K (h : Gₖ)) (embeddedUnitInvariant K E b)

private theorem embeddedUnitCoefficient_transport (b : Eˣ) (a : Zₖ) :
    embeddedUnitsTransport K E j
      ((integralRestrictionCoefficient (embeddedAbsoluteRestrictionHom K E j) ≫
        unitScalarCoefficientMap E b) a) = embeddedInvariantCoefficientMap K E b a := by
  let Y := TopRep.res (H).toSubgroup.subtype (unitsRep K)
  let bE : unitsRep E := Additive.ofMul (α := (SeparableClosure E)ˣ)
    (Units.map (algebraMap E (SeparableClosure E)).toMonoidHom b)
  let bK : Y := Additive.ofMul (α := (SeparableClosure K)ˣ)
    (Units.map (algebraMap E (SeparableClosure K)).toMonoidHom b)
  let n : ℤ := (show ULift.{u} ℤ from a).down
  let ψ := embeddedUnitsTransport K E j
  change ψ (n • bE) = n • bK
  rw [map_smul]
  apply congrArg (fun t : Y => n • t)
  apply Additive.toMul.injective
  apply Units.ext
  exact j.symm.commutes (b : E)

private theorem embeddedIntegralClass_transport (b : Eˣ) (x : continuousCohomology 2 Zₖ) :
    embeddedUnitsCohomologyTransport K E j
      (embeddedUnitsIntegralClass K E j b x) =
      degreeTwoInvariantMap (A := TopRep.res (H).toSubgroup.subtype Zₖ)
        (B := TopRep.res (H).toSubgroup.subtype (unitsRep K))
        (C := TopRep.res (H).toSubgroup.subtype (unitsRep K))
        (unitScalarPairing K) (unitScalarPairing_continuous K)
        (fun h => unitScalarPairing_equivariant K (h : Gₖ))
        (embeddedUnitInvariant K E b) (openRestriction Zₖ H 2 x) := by
  let J := ↥(stageOpenFixingSubgroup K E).toSubgroup
  let r := embeddedAbsoluteRestrictionHom K E j
  let s : J →ₜ* Gₑ := embeddedAbsoluteRestrictionInverseHom K E j
  let i : J →ₜ* Gₖ := ProCGroups.ContinuousMonoidHom.subtype (H).toSubgroup
  let f : TopRep.res r.toMonoidHom Zₖ ⟶ unitsRep E :=
    integralRestrictionCoefficient r ≫ unitScalarCoefficientMap E b
  let g := embeddedUnitsTransport K E j
  let h := embeddedInvariantCoefficientMap K E b
  have hr (σ : J) : r (s σ) = i σ :=
    (embeddedAbsoluteRestrictionEquiv_coe K E j (s σ)).symm.trans
      (congrArg Subtype.val ((embeddedAbsoluteRestrictionEquiv K E j).apply_symm_apply σ))
  exact map_through_restriction (X := Zₖ) (Y := unitsRep E)
    (Z := TopRep.res (H).toSubgroup.subtype (unitsRep K))
    r s i f g h hr (embeddedUnitCoefficient_transport K E j b) x

/-- Corestriction takes the product of a restricted integer class with an
upper-field unit to the product of the original class with its field norm. -/
theorem embeddedAbsoluteBrCorestriction_unitsIntegralClass
    (b : Eˣ) (x : continuousCohomology 2 Zₖ) :
    embeddedAbsoluteBrCorestriction K E j
        (embeddedUnitsIntegralClass K E j b x) =
      unitsIntegralClass K (normUnits K E b) x := by
  change corestrict (unitsRep K) H 2
    (embeddedUnitsCohomologyTransport K E j
      (embeddedUnitsIntegralClass K E j b x)) = _
  rw [embeddedIntegralClass_transport K E j, corestrict_degreeTwoInvariantMap (unitsRep K) H
    (unitScalarPairing K) (unitScalarPairing_continuous K) (unitScalarPairing_equivariant K),
    embeddedUnitInvariant_norm K E]
  rfl

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

attribute [local instance] embeddedStageSpectralNormedField embeddedStageSpectralValuativeRel
  embeddedStageSpectralLocalField

/-- Restriction to an actual finite embedded separable extension is surjective. -/
theorem embeddedAbsoluteBrRestriction_surjective :
    Function.Surjective (embeddedAbsoluteBrRestriction K E j) := by
  intro x
  let d := Module.finrank K E
  obtain ⟨q, hq⟩ := QuotientAddGroup.mk_surjective (localBrauerInvariant E x)
  obtain ⟨y, hy⟩ := (localBrauerInvariantEquiv K).surjective ((q / (d : ℚ) : ℚ) : AddCircle (1 : ℚ))
  refine ⟨y, (localBrauerInvariantEquiv E).injective ?_⟩
  change localBrauerInvariant E (embeddedAbsoluteBrRestriction K E j y) = localBrauerInvariant E x
  rw [localBrauerInvariant_embeddedRestriction]
  change d • (localBrauerInvariantEquiv K) y = _
  rw [hy, ← AddCircle.coe_nsmul, nsmul_eq_mul]
  have hd : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hq' : (d : ℚ) * (q / (d : ℚ)) = q := by field_simp
  exact (congrArg (fun t : ℚ => (t : AddCircle (1 : ℚ))) hq').trans hq

/-- The arithmetic invariant of the actual corestriction is the upper
arithmetic invariant, for the same chosen comparison of closures. -/
theorem localBrauerInvariant_embeddedCorestriction (x : Br E) :
    localBrauerInvariant K (embeddedAbsoluteBrCorestriction K E j x) =
      localBrauerInvariant E x := by
  obtain ⟨x, rfl⟩ := embeddedAbsoluteBrRestriction_surjective K E j x
  rw [embeddedAbsoluteBrCorestriction_restriction, map_nsmul,
    localBrauerInvariant_embeddedRestriction]

end ClassFieldTheory.Brauer

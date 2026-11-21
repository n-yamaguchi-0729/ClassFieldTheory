/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.GlobalFundamentalRestriction
public import Nyll.GaloisCohomology.GroupTheory.H2FiniteIndexTrace

/-! # Corestriction of normalized global fundamental classes -/

@[expose] public section

open CategoryTheory ClassFieldTower.Cohomology
open NumberField

noncomputable section
namespace GlobalClassFieldTheory.Cohomology

section EmbeddedTower

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (M : IntermediateField K L) [NumberField M]

local notation "S" => IntermediateField.fixingSubgroup M
local notation "A" => standardIdeleClassRep K L
local notation "B" => Rep.res (Subgroup.subtype S) A
local notation "H" F => groupCohomology (standardIdeleClassRep F L) 2

/-- Corestriction via the finite-index trace of the ordinary upper idèle-class representation. -/
def standardIdeleClassH2Corestrict : (H M) ⟶ (H K) :=
  (standardIdeleClassRelativeCohomologyIso K L M 2).inv ≫ finiteIndexH2Corestriction A S

/-- Applying corestriction after actual subgroup restriction multiplies
the ordinary degree-two class by the intermediate degree. -/
theorem standardIdeleClassH2Corestrict_restrict (x : H K) :
    standardIdeleClassH2Corestrict K L M (standardIdeleClassH2Restrict K L M x) =
      Module.finrank K M • x := by
  let d := standardIdeleClassRelativeCohomologyIso K L M 2
  change finiteIndexH2Corestriction A S
      (d.inv (d.hom (groupCohomology.map (S).subtype (𝟙 B) 2 x))) = _
  rw [Iso.hom_inv_id_apply]
  simpa only [← IntermediateField.finrank_eq_fixingSubgroup_index L M] using
    finiteIndexH2Corestriction_restrict A S x

/-- Corestriction sends the intermediate normalized class to the actual
index multiple of the top normalized class. -/
theorem canonicalGlobalFundamentalClass_corestrict
    (K₁ : Type) [Field K₁] [NumberField K₁]
    (L₁ : FiniteGaloisIntermediateField K₁ (SeparableClosure K₁)) [NumberField L₁]
    (M₁ : IntermediateField K₁ L₁) [NumberField M₁] :
    let _ : FiniteDimensional M₁ L₁ := Module.Finite.of_restrictScalars_finite K₁ M₁ L₁
    let _ : IsGalois M₁ L₁ := IsGalois.tower_top_of_isGalois K₁ M₁ L₁
    standardIdeleClassH2Corestrict K₁ L₁ M₁ (finiteGlobalFundamentalClass M₁ L₁) =
      Module.finrank K₁ M₁ • canonicalGlobalFundamentalClass K₁ L₁ := by
  intro finOwner galOwner
  rw [← canonicalGlobalFundamentalClass_restrict K₁ L₁ M₁,
    standardIdeleClassH2BaseRestriction_eq_fixingSubgroup]
  exact standardIdeleClassH2Corestrict_restrict K₁ L₁ M₁
    (canonicalGlobalFundamentalClass K₁ L₁)

end EmbeddedTower

section OriginalTower

universe u v w

variable (K : Type u) (F : Type v) (E : Type w)
  [Field K] [NumberField K] [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]

local notation "H₂[" A "]" =>
  IntegralGroupCohomology.Universe.cohomology (standardIdeleClassRep A E) 2
local notation "V[" A "]" =>
  globalFundamentalNativeRep A E
local notation "r" => liftedGaloisBaseRestriction K F E
local notation "S" => MonoidHom.range r
local notation "B" => Rep.res (Subgroup.subtype S) V[K]

/-- The intermediate Galois group identifies with its actual image under scalar restriction. -/
def liftedGaloisBaseRestrictionRangeEquiv : S ≃* ULift.{w} Gal(E/F) :=
  (MulEquiv.ofBijective (r).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr (by
      intro σ τ h
      apply ULift.ext
      apply AlgEquiv.ext
      intro a
      exact congrArg (fun g : ULift.{w} Gal(E/K) => g.down a) h),
      (r).rangeRestrict_surjective⟩).symm

/-- Identifying the subgroup with the intermediate Galois group preserves its actual action. -/
def liftedIdeleClassRelativeH2Iso : groupCohomology B 2 ≅ groupCohomology V[F] 2 :=
  groupCohomology.mapIso (liftedGaloisBaseRestrictionRangeEquiv K F E)
    (LinearEquiv.refl (ULift.{w} ℤ) B) (fun s => by
      let e := liftedGaloisBaseRestrictionRangeEquiv K F E
      have hs : r (e s) = s :=
        congrArg Subtype.val (e.symm_apply_apply s)
      apply LinearMap.ext
      intro a
      change (V[K]).ρ s a = (V[K]).ρ (r (e s)) a
      rw [hs]) 2

/-- Restriction of scalars on cohomology factors through restriction to its image subgroup. -/
theorem originalStandardIdeleClassH2BaseRestriction_eq_range (x : H₂[K]) :
    originalStandardIdeleClassH2BaseRestriction K F E x =
      (liftedIdeleClassRelativeH2Iso K F E).hom (groupCohomology.map (S).subtype (𝟙 B) 2 x) := by
  let z : groupCohomology V[K] 2 := x
  change groupCohomology.map r (liftedIdeleClassBaseRestrictionRepHom K F E) 2 z =
    (liftedIdeleClassRelativeH2Iso K F E).hom (groupCohomology.map (S).subtype (𝟙 B) 2 z)
  unfold liftedIdeleClassRelativeH2Iso groupCohomology.mapIso
  dsimp only
  rw [← ConcreteCategory.comp_apply, ← groupCohomology.map_comp]
  apply ConcreteCategory.congr_hom
  apply groupCohomology.map_congr
  · exact (r).subtype_comp_rangeRestrict.symm
  · apply LinearMap.ext
    intro a
    rfl

variable [FiniteDimensional K E] [IsGalois K E]

/-- Corestrict with the actual subgroup trace on the original idèle class action. -/
def originalStandardIdeleClassH2Corestrict : H₂[F] →+ H₂[K] :=
  ((liftedIdeleClassRelativeH2Iso K F E).inv ≫
    finiteIndexH2Corestriction V[K] S).hom.toAddMonoidHom

variable [FiniteDimensional K F] [FiniteDimensional F E] [IsGalois F E]

omit [NumberField E] in
/-- On the original tower, the index of the actual subgroup is the intermediate degree. -/
theorem liftedGaloisBaseRestriction_range_index : (S).index = Module.finrank K F := by
  have hS : Nat.card S = Module.finrank F E :=
    (Nat.card_congr ((liftedGaloisBaseRestrictionRangeEquiv K F E).trans
      MulEquiv.ulift).toEquiv).trans (IsGalois.card_aut_eq_finrank F E)
  have hG : Nat.card (ULift.{w} Gal(E/K)) = Module.finrank K E :=
    (Nat.card_congr Equiv.ulift).trans (IsGalois.card_aut_eq_finrank K E)
  have h := (S).index_mul_card
  rw [hS, hG, ← Module.finrank_mul_finrank K F E] at h
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h

/-- Corestriction after restriction multiplies by the actual intermediate degree. -/
theorem originalStandardIdeleClassH2Corestrict_restrict (x : H₂[K]) :
    originalStandardIdeleClassH2Corestrict K F E
        (originalStandardIdeleClassH2BaseRestriction K F E x) = Module.finrank K F • x := by
  rw [originalStandardIdeleClassH2BaseRestriction_eq_range]
  let d := liftedIdeleClassRelativeH2Iso K F E
  let z : groupCohomology V[K] 2 := x
  change finiteIndexH2Corestriction V[K] S
      (d.inv (d.hom (groupCohomology.map (S).subtype (𝟙 B) 2 z))) = Module.finrank K F • z
  rw [Iso.hom_inv_id_apply, ← liftedGaloisBaseRestriction_range_index K F E]
  exact finiteIndexH2Corestriction_restrict V[K] S z

/-- Corestriction gives the intermediate degree multiple of the original fundamental class. -/
theorem globalFundamentalClass_corestrict :
    originalStandardIdeleClassH2Corestrict K F E (globalFundamentalClass F E) =
      Module.finrank K F • globalFundamentalClass K E := by
  rw [← globalFundamentalClass_restrict K F E]
  exact originalStandardIdeleClassH2Corestrict_restrict K F E (globalFundamentalClass K E)

end OriginalTower

end GlobalClassFieldTheory.Cohomology

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.IdeleClassBaseInflationSquare
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.IdeleH2KernelByInvariantSum
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.IdeleLocalBrauerRestriction

/-! # Passing between restriction on full idèles and on standard idèle classes -/

@[expose] public section

open CategoryTheory ClassFieldTower.Martinet.Shafarevich NumberField
open scoped NumberField

noncomputable section
namespace GlobalClassFieldTheory.Cohomology

section BaseRestrictionSquare

variable {K M E : Type} [Field K] [NumberField K] [Field M] [NumberField M]
  [Field E] [NumberField E] [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E]
  [FiniteDimensional K M] [FiniteDimensional K E] [FiniteDimensional M E]
  [IsGalois K E] [IsGalois M E]

local notation "q" F =>
  ShortComplex.g (finiteIdeleShortComplex F E) ≫
    Iso.hom (relativeToStandardIdeleClassRepIso F E)
local notation "r" => (AlgEquiv.restrictScalarsHom K : Gal(E/M) →* Gal(E/K))

omit [IsGalois K E] [IsGalois M E] in
/-- On the actual two bases the full idèle quotient commutes with subgroup restriction. -/
theorem fullIdeleClassH2Map_actualBaseRestriction
    (x : groupCohomology (finiteIdeleShortComplex K E).X₂ 2) :
    standardIdeleClassH2BaseRestriction K M E (fullIdeleClassH2Map K E x) =
      fullIdeleClassH2Map M E (fullIdeleH2BaseRestriction (M := M) x) := by
  have h :
      groupCohomology.map (MonoidHom.id _) (q K) 2 ≫
          groupCohomology.map r (standardIdeleClassBaseRestrictionRepHom K M E) 2 =
        groupCohomology.map r
            (relativeIdeleBaseRestrictionRepHom (K₀ := K) (M₀ := M) (L₀ := E)) 2 ≫
          groupCohomology.map (MonoidHom.id _) (q M) 2 := by
    rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
    apply groupCohomology.map_congr (by simp only [MonoidHom.id_comp, MonoidHom.comp_id])
    apply LinearMap.ext
    intro a
    apply Additive.toMul.injective
    let a₀ : Additive (RelativeIdeleGroup K E) := a
    change NumberField.IdeleClassGroup.relativeClassComparison K E
        (QuotientGroup.mk' (RelativeIdeleGroup.principalSubgroup K E) a₀.toMul) =
      NumberField.IdeleClassGroup.relativeClassComparison M E
        (QuotientGroup.mk' (RelativeIdeleGroup.principalSubgroup M E)
          (towerRelativeIdeleBaseChangeMulEquiv K M E
            ((towerRelativeIdeleEquiv K M E).symm a₀.toMul)))
    simp only [NumberField.IdeleClassGroup.relativeClassComparison,
      relativeIdeleClassBaseChangeMulEquiv_mk]
    rw [relativeIdeleBaseChangeMulEquiv_tower, MulEquiv.apply_symm_apply]
  exact ConcreteCategory.congr_hom h x

end BaseRestrictionSquare

variable (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (M : IntermediateField K E) [NumberField M]

omit [FiniteDimensional K E] [IsGalois K E] in
/-- The literal fixing subgroup and the actual Galois group of the
intermediate base give the same restriction on standard idèle classes. -/
theorem standardIdeleClassH2BaseRestriction_eq_fixingSubgroup :
    standardIdeleClassH2BaseRestriction K M E = standardIdeleClassH2Restrict K E M := by
  let X := standardIdeleClassRep K E
  let S := M.fixingSubgroup
  let i := S.subtype
  let r := M.fixingSubgroupEquiv.symm.toMonoidHom
  let φ : Rep.res r (Rep.res i X) ⟶ standardIdeleClassRep M E :=
    Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩
  change groupCohomology.map (AlgEquiv.restrictScalarsHom K)
      (standardIdeleClassBaseRestrictionRepHom K M E) 2 =
    groupCohomology.map i (𝟙 (Rep.res i X)) 2 ≫ groupCohomology.map r φ 2
  rw [← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · apply MonoidHom.ext
    intro a
    rfl
  · rfl

omit [IsGalois K E] in
/-- The quotient map for an actual fixing subgroup commutes with restriction. -/
theorem fullIdeleClassH2Map_baseRestriction
    (x : groupCohomology (finiteIdeleShortComplex K E).X₂ 2) :
    standardIdeleClassH2Restrict K E M (fullIdeleClassH2Map K E x) =
      fullIdeleClassH2Map M E (fullIdeleH2BaseRestriction (M := M) x) := by
  rw [← standardIdeleClassH2BaseRestriction_eq_fixingSubgroup]
  exact fullIdeleClassH2Map_actualBaseRestriction x

end GlobalClassFieldTheory.Cohomology

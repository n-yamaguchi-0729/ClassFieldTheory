/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.FiniteGlobalInvariantLift
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.GlobalFundamentalClass
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.IdeleClassBaseInflationSquare

/-! # Arithmetic restriction of normalized global fundamental classes -/

@[expose] public section

open CategoryTheory ClassFieldTheory.Brauer ClassFieldTower.Martinet.Shafarevich
open IsDedekindDomain NumberField
open scoped NumberField

noncomputable section
namespace GlobalClassFieldTheory.Cohomology

section ArbitraryTower

variable (K M L : Type) [Field K] [NumberField K] [Field M] [NumberField M]
  [Field L] [NumberField L] [Algebra K M] [Algebra K L] [Algebra M L]
  [IsScalarTower K M L] [FiniteDimensional K M] [FiniteDimensional K L]
  [FiniteDimensional M L] [IsGalois K L] [IsGalois M L]

/-- The actual subgroup restriction of the normalized class is the
normalized class of the original finite top field over the intermediate base. -/
theorem finiteGlobalFundamentalClass_restrict :
    standardIdeleClassH2BaseRestriction K M L (finiteGlobalFundamentalClass K L) =
      finiteGlobalFundamentalClass M L := by
  obtain ⟨v⟩ := finitePlace_nonempty K
  obtain ⟨E, j, x, b, hxClass, hx, hb⟩ := finiteGlobalFundamentalClass_onePlaceWitness K L v
  let : NumberField E := NumberField.of_module_finite K E
  let : Algebra L E := j.toRingHom.toAlgebra
  let : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq fun a => (j.commutes a).symm
  let : Algebra M E := ((algebraMap L E).comp (algebraMap M L)).toAlgebra
  let : IsScalarTower M L E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower K M E := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap K E a = algebraMap L E (algebraMap M L (algebraMap K M a))
    rw [← IsScalarTower.algebraMap_apply K M L, ← IsScalarTower.algebraMap_apply K L E]
  let : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite K M E
  let : IsGalois M E := IsGalois.tower_top_of_isGalois K M E
  let jM : L →ₐ[M] E := IsScalarTower.toAlgHom M L E
  let y := fullIdeleH2BaseRestriction (M := M) x
  let u := finiteGlobalFundamentalClass K L
  let z := standardIdeleClassH2BaseRestriction K M L u
  let T := finiteGlobalInvariantStage M E
  let : NumberField T := NumberField.of_module_finite M T
  let k := (finiteGlobalInvariantStageEquiv M E).toAlgHom
  let w := fullIdeleH2InflateOfEmbedding k y
  have hm := ConcreteCategory.congr_hom (standardIdeleClassH2BaseRestriction_inflate K M jM) u
  change standardIdeleClassH2BaseRestriction K M E
      (standardIdeleClassH2InflateOfEmbedding j u) =
    standardIdeleClassH2InflateOfEmbedding jM z at hm
  rw [hxClass, fullIdeleClassH2Map_actualBaseRestriction] at hm
  have hq : fullIdeleBrauerInvariantSum M T w =
      ((1 / (Module.finrank M L : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
    change sumLocalInv M (fullIdeleBrauerTuple M T (fullIdeleH2InflateOfEmbedding k y)) = _
    rw [fullIdeleBrauerTuple_inflateOfEmbedding]
    change fullIdeleBrauerInvariantSum M E y = _
    rw [fullIdeleBrauerInvariantSum_baseRestriction_single v b x hx, hb]
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
    apply congrArg (fun a : ℚ => (a : AddCircle (1 : ℚ)))
    rw [← Module.finrank_mul_finrank K M L, Nat.cast_mul]
    have h : (Module.finrank K M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    rw [mul_one_div, ← mul_div_mul_left (1 : ℚ) (Module.finrank M L : ℚ) h, mul_one]
  have hz : HasFiniteGlobalInvariant M L z
      ((1 / (Module.finrank M L : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
    refine ⟨T, k.comp jM, w, ?_, hq⟩
    rw [standardIdeleClassH2InflateOfEmbedding_comp]
    change standardIdeleClassH2InflateOfEmbedding k (standardIdeleClassH2InflateOfEmbedding jM z) =
      _
    rw [← hm, fullIdeleClassH2Map_inflateOfEmbedding]
  exact HasFiniteGlobalInvariant.eq M L hz (finiteGlobalFundamentalClass_spec M L)

end ArbitraryTower

section EmbeddedTower

variable (K : Type) [Field K] [NumberField K]
  (L : FiniteGaloisIntermediateField K (SeparableClosure K)) [NumberField L]
  (M : IntermediateField K L) [NumberField M]

/-- The same restriction formula for a given finite stage and its
intermediate field. -/
theorem canonicalGlobalFundamentalClass_restrict :
    let _ : FiniteDimensional M L := Module.Finite.of_restrictScalars_finite K M L
    let _ : IsGalois M L := IsGalois.tower_top_of_isGalois K M L
    standardIdeleClassH2BaseRestriction K M L (canonicalGlobalFundamentalClass K L) =
      finiteGlobalFundamentalClass M L := by
  intro finOwner galOwner
  rw [← finiteGlobalFundamentalClass_eq_canonical K L]
  exact finiteGlobalFundamentalClass_restrict K M L

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

/-- The original restriction of scalars on the acting groups of the lifted representations. -/
def liftedGaloisBaseRestriction : ULift.{w} Gal(E/F) →* ULift.{w} Gal(E/K) :=
  MulEquiv.ulift.symm.toMonoidHom.comp
    ((AlgEquiv.restrictScalarsHom K).comp MulEquiv.ulift.toMonoidHom)

/-- Restriction keeps the original top field's lifted idèle class coefficients. -/
def liftedIdeleClassBaseRestrictionRepHom :
    Rep.res (liftedGaloisBaseRestriction K F E) V[K] ⟶ V[F] :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

/-- Restrict the actual Galois action on the same idèle class coefficients. -/
def originalStandardIdeleClassH2BaseRestriction :
    groupCohomology V[K] 2 →+ groupCohomology V[F] 2 :=
  (groupCohomology.map (liftedGaloisBaseRestriction K F E)
    (liftedIdeleClassBaseRestrictionRepHom K F E) 2).hom.toAddMonoidHom

variable [FiniteDimensional K F] [FiniteDimensional K E] [FiniteDimensional F E]
  [IsGalois K E] [IsGalois F E]

attribute [local instance] ClassFieldTheory.numberField_small ClassFieldTheory.numberField_shrink
attribute [local instance] HasseArf.shrinkAlgebra HasseArf.shrink_finiteDimensional
attribute [local instance] shrinkNumberField_isGalois
attribute [local instance] HasseArf.shrink_isScalarTower

local notation "K₀" => (Shrink K : Type)
local notation "F₀" => (Shrink F : Type)
local notation "E₀" => (Shrink E : Type)

omit [FiniteDimensional K F] [FiniteDimensional K E] [FiniteDimensional F E]
  [IsGalois K E] [IsGalois F E] in
private theorem shrinkGaloisBaseRestriction_commutes (σ : ULift.{w} Gal(E/F)) :
    globalFundamentalShrinkH2GroupEquiv K E (liftedGaloisBaseRestriction K F E σ) =
      (globalFundamentalShrinkH2GroupEquiv F E σ).restrictScalars K₀ := by
  let gK := HasseArf.shrinkGalMulEquiv K E
  let gF := HasseArf.shrinkGalMulEquiv F E
  change gK.symm (σ.down.restrictScalars K) = (gF.symm σ.down).restrictScalars K₀
  apply gK.injective
  rw [gK.apply_symm_apply]
  have he := ClassFieldTheory.restrictScalars_galEquiv_of_equiv_equiv (Shrink.ringEquiv K).symm
    (Shrink.ringEquiv F).symm (Shrink.ringEquiv E).symm
    (HasseArf.shrinkAlgebra_commutes K E) (HasseArf.shrinkAlgebra_commutes F E) (gF.symm σ.down)
  change (gF (gF.symm σ.down)).restrictScalars K =
    gK ((gF.symm σ.down).restrictScalars K₀) at he
  rwa [gF.apply_symm_apply] at he

omit [FiniteDimensional K F] [FiniteDimensional K E] [FiniteDimensional F E]
  [IsGalois K E] [IsGalois F E] in
private theorem shrinkStandardIdeleClassH2BaseRestriction_apply
    (x : groupCohomology V[K] 2) :
    globalFundamentalShrinkH2Equiv F E (originalStandardIdeleClassH2BaseRestriction K F E x) =
      standardIdeleClassH2BaseRestriction K₀ F₀ E₀ (globalFundamentalShrinkH2Equiv K E x) := by
  have h := groupCohomology.equivariantH2AddEquiv_map
    (A := V[K]) (B := standardIdeleClassRep K₀ E₀)
    (A' := V[F]) (B' := standardIdeleClassRep F₀ E₀)
    (globalFundamentalShrinkH2GroupEquiv K E)
    (globalFundamentalShrinkH2CoefficientEquiv K E)
    (globalFundamentalShrinkH2_equivariant K E)
    (globalFundamentalShrinkH2GroupEquiv F E)
    (globalFundamentalShrinkH2CoefficientEquiv F E)
    (globalFundamentalShrinkH2_equivariant F E)
    (liftedGaloisBaseRestriction K F E) (AlgEquiv.restrictScalarsHom K₀)
    (liftedIdeleClassBaseRestrictionRepHom K F E)
    (standardIdeleClassBaseRestrictionRepHom K₀ F₀ E₀)
    (shrinkGaloisBaseRestriction_commutes K F E) (fun _ => rfl) x
  dsimp only [globalFundamentalShrinkH2Equiv, originalStandardIdeleClassH2BaseRestriction,
      standardIdeleClassH2BaseRestriction, LinearMap.toAddMonoidHom_coe,
      ModuleCat.Hom.hom, groupCohomology.H2,
    shrinkSemiring_eq_fieldSemiring, shrinkCommSemiring_eq_fieldCommSemiring] at h ⊢
  with_reducible_and_instances exact h

/-- The normalized class restricts to the normalized class over the actual
intermediate base, with the fields in independent universes. -/
theorem globalFundamentalClass_restrict :
    originalStandardIdeleClassH2BaseRestriction K F E (globalFundamentalClass K E) =
      globalFundamentalClass F E := by
  apply (globalFundamentalShrinkH2Equiv F E).injective
  have h := shrinkStandardIdeleClassH2BaseRestriction_apply K F E (globalFundamentalClass K E)
  have hleft := congrArg (standardIdeleClassH2BaseRestriction K₀ F₀ E₀)
    (globalFundamentalShrinkH2Equiv_globalFundamentalClass K E)
  exact h.trans (hleft.trans ((finiteGlobalFundamentalClass_restrict K₀ F₀ E₀).trans
    (globalFundamentalShrinkH2Equiv_globalFundamentalClass F E).symm))

end OriginalTower

end GlobalClassFieldTheory.Cohomology

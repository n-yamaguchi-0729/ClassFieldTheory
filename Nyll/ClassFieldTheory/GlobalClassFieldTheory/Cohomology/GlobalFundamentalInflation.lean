/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.FiniteGlobalInvariantLift
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.GlobalFundamentalClass
public import Nyll.GaloisCohomology.GroupTheory.H2EquivariantPullback

/-! # Arithmetic inflation of normalized global fundamental classes -/

@[expose] public section

open CategoryTheory ClassFieldTheory.Brauer NumberField
open scoped NumberField

noncomputable section
namespace GlobalClassFieldTheory.Cohomology

section ArbitraryTower

variable (K L M : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Field M] [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M]
  [IsScalarTower K L M] [FiniteDimensional K L] [FiniteDimensional K M]
  [FiniteDimensional L M] [IsGalois K L] [IsGalois K M]

/-- Standard inflation multiplies the normalized fundamental class of the
larger finite Galois extension by the actual intermediate degree. -/
theorem finiteGlobalFundamentalClass_inflate :
    standardIdeleClassH2InflateOfEmbedding (IsScalarTower.toAlgHom K L M)
      (finiteGlobalFundamentalClass K L) =
      Module.finrank L M • finiteGlobalFundamentalClass K M := by
  let i := IsScalarTower.toAlgHom K L M
  let n := Module.finrank L M
  let u := finiteGlobalFundamentalClass K L
  let v := finiteGlobalFundamentalClass K M
  obtain ⟨E, i₁, x, hx, hxq⟩ := finiteGlobalFundamentalClass_spec K L
  obtain ⟨F, i₂, y, hy, hyq⟩ := finiteGlobalFundamentalClass_spec K M
  let T := E ⊔ F
  let : NumberField E := NumberField.of_module_finite K E
  let : NumberField F := NumberField.of_module_finite K F
  let : NumberField T := NumberField.of_module_finite K T
  let j₁ : E →ₐ[K] T :=
    IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff E T).mp le_sup_left)
  let j₂ : F →ₐ[K] T :=
    IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff F T).mp le_sup_right)
  let k := j₂.comp i₂
  have hk := standardIdeleClassH2InflateOfEmbedding_eq_of_embeddings K L
    (k.comp i) (j₁.comp i₁)
  let a := fullIdeleH2InflateOfEmbedding j₁ x
  let b := fullIdeleH2InflateOfEmbedding j₂ y
  have ha : standardIdeleClassH2InflateOfEmbedding k (standardIdeleClassH2InflateOfEmbedding i u) =
      fullIdeleClassH2Map K T a := by
    change (standardIdeleClassH2InflateOfEmbedding i ≫
      standardIdeleClassH2InflateOfEmbedding k) u = _
    rw [← standardIdeleClassH2InflateOfEmbedding_comp, hk,
      standardIdeleClassH2InflateOfEmbedding_comp]
    change standardIdeleClassH2InflateOfEmbedding j₁
      (standardIdeleClassH2InflateOfEmbedding i₁ u) = _
    rw [hx, fullIdeleClassH2Map_inflateOfEmbedding]
  have hb : standardIdeleClassH2InflateOfEmbedding k v = fullIdeleClassH2Map K T b := by
    change standardIdeleClassH2InflateOfEmbedding (j₂.comp i₂) v = _
    rw [standardIdeleClassH2InflateOfEmbedding_comp]
    change standardIdeleClassH2InflateOfEmbedding j₂
      (standardIdeleClassH2InflateOfEmbedding i₂ v) = _
    rw [hy, fullIdeleClassH2Map_inflateOfEmbedding]
  have hrat :
      n • ((1 / (Module.finrank K M : ℚ) : ℚ) : AddCircle (1 : ℚ)) =
        ((1 / (Module.finrank K L : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
    apply congrArg (fun x : ℚ => (x : AddCircle (1 : ℚ)))
    rw [← Module.finrank_mul_finrank K L M, Nat.cast_mul]
    have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    change (n : ℚ) * (1 / ((Module.finrank K L : ℚ) * (n : ℚ))) = _
    calc
      _ = (n : ℚ) / ((n : ℚ) * Module.finrank K L) := by
        rw [mul_one_div, mul_comm (Module.finrank K L : ℚ) (n : ℚ)]
      _ = _ := by rw [← mul_div_mul_left (1 : ℚ) (Module.finrank K L : ℚ) hn, mul_one]
  have hsum : fullIdeleBrauerInvariantSum K T (a - n • b) = 0 := by
    rw [map_sub, map_nsmul]
    change sumLocalInv K (fullIdeleBrauerTuple K T a) -
      n • sumLocalInv K (fullIdeleBrauerTuple K T b) = 0
    rw [fullIdeleBrauerTuple_inflateOfEmbedding, fullIdeleBrauerTuple_inflateOfEmbedding]
    change fullIdeleBrauerInvariantSum K E x - n • fullIdeleBrauerInvariantSum K F y = 0
    rw [hxq, hyq, hrat, sub_self]
  have hclass : fullIdeleClassH2Map K T (a - n • b) = 0 :=
    fullIdeleClassH2Map_eq_zero_of_invariantSum K T _ hsum
  apply standardIdeleClassH2InflateOfEmbedding_injective K k
  change standardIdeleClassH2InflateOfEmbedding k (standardIdeleClassH2InflateOfEmbedding i u) =
    (standardIdeleClassH2InflateOfEmbedding k).hom (n • v)
  rw [map_nsmul, ha, hb]
  rw [map_sub, map_nsmul] at hclass
  exact sub_eq_zero.mp hclass

end ArbitraryTower

section EmbeddedTower

variable (K : Type) [Field K] [NumberField K]
  (L M : FiniteGaloisIntermediateField K (SeparableClosure K)) [NumberField L] [NumberField M]

/-- The same inflation formula for two ordered stages in the separable closure. -/
theorem canonicalGlobalFundamentalClass_inflate (hLM : L ≤ M) :
    let i : L →ₐ[K] M :=
      IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff L M).mp hLM)
    let _ : Algebra L M := i.toRingHom.toAlgebra
    standardIdeleClassH2InflateOfEmbedding i (canonicalGlobalFundamentalClass K L) =
      Module.finrank L M • canonicalGlobalFundamentalClass K M := by
  intro i inclusionAlgebra
  let : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun a => (i.commutes a).symm
  let : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite K L M
  have hi : IsScalarTower.toAlgHom K L M = i := AlgHom.ext (fun _ => rfl)
  rw [← finiteGlobalFundamentalClass_eq_canonical K L,
    ← finiteGlobalFundamentalClass_eq_canonical K M, ← hi]
  exact finiteGlobalFundamentalClass_inflate K L M

end EmbeddedTower

section OriginalTower

universe u v w

variable (K : Type u) (F : Type v) (E : Type w)
  [Field K] [NumberField K] [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E] [IsGalois K F]

local notation "H₂[" A "]" =>
  IntegralGroupCohomology.Universe.cohomology (standardIdeleClassRep K A) 2
local notation "V[" A "]" =>
  globalFundamentalNativeRep K A

/-- The actual restriction of a Galois automorphism to the normal intermediate extension. -/
def liftedGaloisNormalRestriction : ULift.{w} Gal(E/K) →* ULift.{v} Gal(F/K) :=
  MulEquiv.ulift.symm.toMonoidHom.comp
    ((AlgEquiv.restrictNormalHom F).comp MulEquiv.ulift.toMonoidHom)

/-- The actual inclusion of the idèle class coefficients in the upper extension. -/
def liftedIdeleClassFieldInclusion : V[F] →+ V[E] :=
  AddEquiv.ulift.symm.toAddMonoidHom.comp
    ((NumberField.IdeleClassGroup.fieldInclusion F E).toAdditive.comp
      AddEquiv.ulift.toAddMonoidHom)

/-- Idèle class inclusion intertwines the action through actual Galois restriction. -/
theorem liftedIdeleClassFieldInclusion_equivariant
    (σ : ULift.{w} Gal(E/K)) (c : V[F]) :
    liftedIdeleClassFieldInclusion K F E ((V[F]).ρ (liftedGaloisNormalRestriction K F E σ) c) =
      (V[E]).ρ σ (liftedIdeleClassFieldInclusion K F E c) := by
  let r := AlgEquiv.restrictNormalHom F σ.down
  apply ULift.ext
  apply Additive.toMul.injective
  change NumberField.IdeleClassGroup.fieldInclusion F E
      (NumberField.IdeleClassGroup.congr (r.restrictScalars ℚ) c.down.toMul) =
    NumberField.IdeleClassGroup.congr (σ.down.restrictScalars ℚ)
      (NumberField.IdeleClassGroup.fieldInclusion F E c.down.toMul)
  exact (NumberField.IdeleClassGroup.congr_fieldInclusion (r.restrictScalars ℚ)
    (σ.down.restrictScalars ℚ) (fun a => (AlgEquiv.restrictNormal_commutes σ.down F a).symm)
    c.down.toMul).symm

/-- Inflate through actual Galois restriction and standard idèle class inclusion. -/
def originalStandardIdeleClassH2Inflate : H₂[F] →+ H₂[E] :=
  groupCohomology.H2EquivariantPullback (A := V[F]) (B := V[E])
    (liftedGaloisNormalRestriction K F E) (liftedIdeleClassFieldInclusion K F E)
    (liftedIdeleClassFieldInclusion_equivariant K F E)

variable [FiniteDimensional K F] [FiniteDimensional K E] [FiniteDimensional F E] [IsGalois K E]

attribute [local instance] ClassFieldTheory.numberField_small ClassFieldTheory.numberField_shrink
attribute [local instance] HasseArf.shrinkAlgebra HasseArf.shrink_finiteDimensional
attribute [local instance] shrinkNumberField_isGalois
attribute [local instance] HasseArf.shrink_isScalarTower

local notation "K₀" => (Shrink K : Type)
local notation "F₀" => (Shrink F : Type)
local notation "E₀" => (Shrink E : Type)

omit [FiniteDimensional K F] [FiniteDimensional K E] [FiniteDimensional F E]
  [IsGalois K E] in
private theorem shrinkGaloisNormalRestriction_commutes (σ : ULift.{w} Gal(E/K)) :
    globalFundamentalShrinkH2GroupEquiv K F (liftedGaloisNormalRestriction K F E σ) =
      embeddedGaloisRestriction (B := K₀) (IsScalarTower.toAlgHom K₀ F₀ E₀)
        (globalFundamentalShrinkH2GroupEquiv K E σ) := by
  let j := IsScalarTower.toAlgHom K₀ F₀ E₀
  let gF := HasseArf.shrinkGalMulEquiv K F
  let gE := HasseArf.shrinkGalMulEquiv K E
  let τ := gE.symm σ.down
  have hτ : embeddedGaloisRestriction (B := K₀) j τ =
      AlgEquiv.restrictNormalHom F₀ τ := by
    apply AlgEquiv.ext
    intro a
    apply j.injective
    exact (embeddedGaloisRestriction_commutes (B := K₀) j τ a).trans
      (AlgEquiv.restrictNormal_commutes τ F₀ a).symm
  change gF.symm (AlgEquiv.restrictNormalHom F σ.down) =
    embeddedGaloisRestriction (B := K₀) j τ
  rw [hτ]
  apply gF.injective
  rw [gF.apply_symm_apply]
  have he := ClassFieldTheory.restrictNormal_galEquiv_of_equiv_equiv (Shrink.ringEquiv K).symm
    (Shrink.ringEquiv F).symm (Shrink.ringEquiv E).symm
    (HasseArf.shrinkAlgebra_commutes K F) (HasseArf.shrinkAlgebra_commutes K E)
    (HasseArf.shrinkAlgebra_commutes F E) τ
  change AlgEquiv.restrictNormalHom F (gE τ) = gF (AlgEquiv.restrictNormalHom F₀ τ) at he
  rwa [show gE τ = σ.down from gE.apply_symm_apply σ.down] at he

omit [FiniteDimensional K F] [FiniteDimensional K E] [FiniteDimensional F E]
  [IsGalois K E] in
private theorem shrinkIdeleClassFieldInclusion_commutes (c : V[F]) :
    globalFundamentalShrinkH2CoefficientEquiv K E (liftedIdeleClassFieldInclusion K F E c) =
      standardIdeleClassInflationRepHom (IsScalarTower.toAlgHom K₀ F₀ E₀)
        (globalFundamentalShrinkH2CoefficientEquiv K F c) := by
  let j := IsScalarTower.toAlgHom K₀ F₀ E₀
  let eF := (Shrink.ringEquiv F).symm.toRatAlgEquiv
  let eE := (Shrink.ringEquiv E).symm.toRatAlgEquiv
  have hj : embeddedIdeleClassInclusion j = NumberField.IdeleClassGroup.fieldInclusion F₀ E₀ := by
    unfold embeddedIdeleClassInclusion
    change @NumberField.IdeleClassGroup.fieldInclusion F₀ E₀ _ _ _ _
      (algebraMap F₀ E₀).toAlgebra = _
    rw [toAlgebra_algebraMap]
  let c₀ : Additive (NumberField.IdeleClassGroup (𝓞 F) F) := c.down
  let t := Additive.toMul c₀
  apply Additive.toMul.injective
  change NumberField.IdeleClassGroup.congr eE
      (NumberField.IdeleClassGroup.fieldInclusion F E t) =
    embeddedIdeleClassInclusion j (NumberField.IdeleClassGroup.congr eF t)
  rw [hj]
  exact NumberField.IdeleClassGroup.congr_fieldInclusion eF eE
    (fun a => (DFunLike.congr_fun (HasseArf.shrinkAlgebra_commutes F E) a).symm) t

omit [FiniteDimensional K F] [FiniteDimensional K E] [FiniteDimensional F E]
  [IsGalois K E] in
private theorem shrinkStandardIdeleClassH2Inflate_apply (x : H₂[F]) :
    globalFundamentalShrinkH2Equiv K E (originalStandardIdeleClassH2Inflate K F E x) =
      standardIdeleClassH2InflateOfEmbedding (IsScalarTower.toAlgHom K₀ F₀ E₀)
        (globalFundamentalShrinkH2Equiv K F x) := by
  let j := IsScalarTower.toAlgHom K₀ F₀ E₀
  have h := groupCohomology.equivariantH2AddEquiv_pullback
    (A := V[F]) (B := V[E]) (A' := standardIdeleClassRep K₀ F₀)
    (B' := standardIdeleClassRep K₀ E₀)
    (liftedGaloisNormalRestriction K F E) (liftedIdeleClassFieldInclusion K F E)
    (liftedIdeleClassFieldInclusion_equivariant K F E)
    (globalFundamentalShrinkH2GroupEquiv K F)
    (globalFundamentalShrinkH2CoefficientEquiv K F)
    (globalFundamentalShrinkH2_equivariant K F)
    (globalFundamentalShrinkH2GroupEquiv K E)
    (globalFundamentalShrinkH2CoefficientEquiv K E)
    (globalFundamentalShrinkH2_equivariant K E)
    (embeddedGaloisRestriction (B := K₀) j).toMonoidHom
    (standardIdeleClassInflationRepHom j)
    (shrinkGaloisNormalRestriction_commutes K F E)
    (shrinkIdeleClassFieldInclusion_commutes K F E) x
  dsimp only [globalFundamentalShrinkH2Equiv, originalStandardIdeleClassH2Inflate,
      standardIdeleClassH2InflateOfEmbedding, groupCohomology.H2, j,
    shrinkSemiring_eq_fieldSemiring, shrinkCommSemiring_eq_fieldCommSemiring] at h ⊢
  with_reducible_and_instances exact h

/-- Inflation in the original universes multiplies the finite Galois fundamental
class by the degree of the upper extension over the intermediate field. -/
theorem globalFundamentalClass_inflate :
    originalStandardIdeleClassH2Inflate K F E (globalFundamentalClass K F) =
      Module.finrank F E • globalFundamentalClass K E := by
  let j := IsScalarTower.toAlgHom K₀ F₀ E₀
  have hdegree : Module.finrank F E = Module.finrank F₀ E₀ :=
    Algebra.finrank_eq_of_equiv_equiv (Shrink.ringEquiv F).symm (Shrink.ringEquiv E).symm
      (HasseArf.shrinkAlgebra_commutes F E)
  apply (globalFundamentalShrinkH2Equiv K E).injective
  have h := shrinkStandardIdeleClassH2Inflate_apply K F E (globalFundamentalClass K F)
  have hleft := congrArg (standardIdeleClassH2InflateOfEmbedding j)
    (globalFundamentalShrinkH2Equiv_globalFundamentalClass K F)
  let c : groupCohomology V[E] 2 := globalFundamentalClass K E
  have hc : globalFundamentalShrinkH2Equiv K E c = finiteGlobalFundamentalClass K₀ E₀ :=
    globalFundamentalShrinkH2Equiv_globalFundamentalClass K E
  have hright : Module.finrank F₀ E₀ • finiteGlobalFundamentalClass K₀ E₀ =
      globalFundamentalShrinkH2Equiv K E (Module.finrank F E • c) := by
    rw [map_nsmul, hc, hdegree]
  exact h.trans (hleft.trans ((finiteGlobalFundamentalClass_inflate K₀ F₀ E₀).trans hright))

end OriginalTower

end GlobalClassFieldTheory.Cohomology

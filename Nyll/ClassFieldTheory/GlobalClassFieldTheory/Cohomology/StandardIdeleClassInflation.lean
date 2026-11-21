/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteBaseChange
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.StandardFieldInclusion
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.IdeleClassH2Tower

/-! # Inflation on standard idèle classes using actual field embeddings -/

@[expose] public section

open CategoryTheory ClassFieldTheory.Brauer ClassFieldTower.Cohomology NumberField
open scoped NumberField

noncomputable section
namespace GlobalClassFieldTheory.Cohomology

variable {K M E T : Type} [Field K] [NumberField K] [Field M] [NumberField M]
  [Field E] [NumberField E] [Field T] [NumberField T] [Algebra K M] [Algebra K E] [Algebra K T]
  [Normal K M] [Normal K E]

local notation "IdeleClasses[" F "]" => NumberField.IdeleClassGroup (𝓞 F) F

/-- The original inclusion of standard idèle classes along an explicit field embedding. -/
def embeddedIdeleClassInclusion (j : M →ₐ[K] E) : IdeleClasses[M] →* IdeleClasses[E] :=
  let _ : Algebra M E := j.toRingHom.toAlgebra
  NumberField.IdeleClassGroup.fieldInclusion M E

/-- The original scalar inclusion is a coefficient map for inflation. -/
def standardIdeleClassInflationRepHom (j : M →ₐ[K] E) :
    Rep.res (embeddedGaloisRestriction (B := K) j).toMonoidHom (standardIdeleClassRep K M) ⟶
      standardIdeleClassRep K E := by
  refine Rep.ofHom ⟨(embeddedIdeleClassInclusion j).toAdditive.toIntLinearMap, fun σ => ?_⟩
  apply LinearMap.ext
  intro a
  apply Additive.toMul.injective
  let _ : Algebra M E := j.toRingHom.toAlgebra
  exact (NumberField.IdeleClassGroup.congr_fieldInclusion
    ((embeddedGaloisRestriction (B := K) j σ).restrictScalars ℚ) (σ.restrictScalars ℚ)
    (fun x => (embeddedGaloisRestriction_commutes (B := K) j σ x).symm) a.toMul).symm

/-- Inflation along the actual inclusion of a finite normal extension. -/
def standardIdeleClassH2InflateOfEmbedding (j : M →ₐ[K] E) :
    groupCohomology (standardIdeleClassRep K M) 2 ⟶
      groupCohomology (standardIdeleClassRep K E) 2 :=
  groupCohomology.map (embeddedGaloisRestriction (B := K) j).toMonoidHom
    (standardIdeleClassInflationRepHom j) 2

omit [NumberField K] [NumberField M] [NumberField E] [NumberField T] in
/-- Restriction along the composite of two normal-field embeddings is the
composite of the original Galois homomorphisms. -/
theorem embeddedGaloisRestriction_comp_hom (j : M →ₐ[K] E) (i : E →ₐ[K] T) :
    (embeddedGaloisRestriction (B := K) (i.comp j)).toMonoidHom =
      (embeddedGaloisRestriction (B := K) j).toMonoidHom.comp
        (embeddedGaloisRestriction (B := K) i).toMonoidHom := by
  apply MonoidHom.ext
  intro σ
  apply AlgEquiv.ext
  intro a
  apply (i.comp j).injective
  let r := embeddedGaloisRestriction (B := K) j
  let t := embeddedGaloisRestriction (B := K) i
  change (i.comp j) (embeddedGaloisRestriction (B := K) (i.comp j) σ a) =
    i (j (r (t σ) a))
  calc
    _ = σ (i (j a)) := embeddedGaloisRestriction_commutes (i.comp j) σ a
    _ = i (t σ (j a)) := (embeddedGaloisRestriction_commutes i σ (j a)).symm
    _ = i (j (r (t σ) a)) := congrArg i (embeddedGaloisRestriction_commutes j (t σ) a).symm

/-- The maps on actual standard cohomology compose along refinements. -/
theorem standardIdeleClassH2InflateOfEmbedding_comp (j : M →ₐ[K] E) (i : E →ₐ[K] T) :
    standardIdeleClassH2InflateOfEmbedding (i.comp j) =
      standardIdeleClassH2InflateOfEmbedding j ≫ standardIdeleClassH2InflateOfEmbedding i := by
  rw [standardIdeleClassH2InflateOfEmbedding, standardIdeleClassH2InflateOfEmbedding,
    standardIdeleClassH2InflateOfEmbedding, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr (embeddedGaloisRestriction_comp_hom j i)
  apply LinearMap.ext
  intro a
  apply Additive.toMul.injective
  let _ : Algebra M E := j.toRingHom.toAlgebra
  let _ : Algebra E T := i.toRingHom.toAlgebra
  let _ : Algebra M T := (i.comp j).toRingHom.toAlgebra
  let _ : IsScalarTower M E T := IsScalarTower.of_algebraMap_eq' rfl
  change embeddedIdeleClassInclusion (i.comp j) a.toMul =
    embeddedIdeleClassInclusion i (embeddedIdeleClassInclusion j a.toMul)
  exact (DFunLike.congr_fun (NumberField.IdeleClassGroup.fieldInclusion_comp M T E) a.toMul).symm

section EmbeddedSubfield

variable (K E) [FiniteDimensional K E] [IsGalois K E]
  (J : IntermediateField K E) [NumberField J] [Normal K J]

omit [Normal K E] in
/-- On an actual intermediate field, quotient inflation agrees with the
map induced by restriction of automorphisms and scalar inclusion of idèle classes. -/
theorem standardIdeleClassH2Inflate_eq_inflateOfEmbedding :
    standardIdeleClassH2Inflate K E J = standardIdeleClassH2InflateOfEmbedding J.val := by
  rw [standardIdeleClassH2Inflate, standardIdeleClassH2InflateOfEmbedding,
    groupCohomology.infNatTrans_app]
  unfold standardIdeleClassQuotientCohomologyIso groupCohomology.mapIso
  dsimp only
  let ker := (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) J).ker
  let e := (restrictionQuotientEquiv K E J).symm.symm.toMonoidHom
  let q := QuotientGroup.mk' ker
  let V := standardIdeleClassRep K E
  let U := standardIdeleClassRep K (↥J)
  let W := V.quotientToInvariants ker
  let β : Rep.res q W ⟶ V := Rep.ofHom (V.ρ.quotientToInvariants_lift ker)
  refine (groupCohomology.map_comp (A := U) (B := W) (C := V) e q _ β 2).symm.trans ?_
  apply groupCohomology.map_congr
  · apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro a
    apply J.val.injective
    change J.val ((restrictionQuotientEquiv K E J (QuotientGroup.mk σ)) a) =
      J.val (embeddedGaloisRestriction (B := K) J.val σ a)
    change J.val (σ.restrictNormal J a) = J.val (embeddedGaloisRestriction (B := K) J.val σ a)
    exact (AlgEquiv.restrictNormal_commutes σ J a).trans
      (embeddedGaloisRestriction_commutes (B := K) J.val σ a).symm
  · apply LinearMap.ext
    intro a
    let w : (Rep.res ker.subtype V).ρ.invariants := standardIdeleClassKernelInvariantsEquiv K E J a
    change w.val = Additive.ofMul (embeddedIdeleClassInclusion J.val a.toMul)
    rfl

end EmbeddedSubfield

end GlobalClassFieldTheory.Cohomology

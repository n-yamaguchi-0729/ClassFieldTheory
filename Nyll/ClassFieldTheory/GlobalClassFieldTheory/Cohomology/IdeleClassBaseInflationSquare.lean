/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.StandardIdeleClassInflation

/-! # Restriction of the base commutes with inflation of the top field -/

@[expose] public section

open CategoryTheory ClassFieldTheory.Brauer

noncomputable section
namespace GlobalClassFieldTheory.Cohomology

section BaseChange

variable (K M E : Type) [Field K] [NumberField K] [Field M] [NumberField M]
  [Field E] [NumberField E]
  [Algebra K M] [Algebra M E] [Algebra K E] [IsScalarTower K M E]

/-- When restricting the base, standard idèle classes keep their original
carrier and the action of an automorphism is unchanged. -/
def standardIdeleClassBaseRestrictionRepHom :
    Rep.res (AlgEquiv.restrictScalarsHom K : Gal(E/M) →* Gal(E/K))
      (standardIdeleClassRep K E) ⟶ standardIdeleClassRep M E :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

/-- Restrict the standard degree-two class with its original coefficient action. -/
def standardIdeleClassH2BaseRestriction :
    groupCohomology (standardIdeleClassRep K E) 2 ⟶
      groupCohomology (standardIdeleClassRep M E) 2 :=
  groupCohomology.map (AlgEquiv.restrictScalarsHom K)
    (standardIdeleClassBaseRestrictionRepHom K M E) 2

end BaseChange

variable (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M]
  {L E : Type} [Field L] [NumberField L] [Field E] [NumberField E]
  [Algebra K M] [Algebra K L] [Algebra K E] [Algebra M L] [Algebra M E]
  [IsScalarTower K M L] [IsScalarTower K M E] [Normal K L] [Normal M L]

/-- The two actual Galois pullbacks commute with the scalar inclusion on
standard idèle classes. -/
theorem standardIdeleClassH2BaseRestriction_inflate (i : L →ₐ[M] E) :
    standardIdeleClassH2InflateOfEmbedding (i.restrictScalars K) ≫
      standardIdeleClassH2BaseRestriction K M E =
    standardIdeleClassH2BaseRestriction K M L ≫ standardIdeleClassH2InflateOfEmbedding i := by
  rw [standardIdeleClassH2InflateOfEmbedding, standardIdeleClassH2BaseRestriction,
    standardIdeleClassH2BaseRestriction, standardIdeleClassH2InflateOfEmbedding,
    ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    apply i.injective
    change (i.restrictScalars K)
        (embeddedGaloisRestriction (B := K) (i.restrictScalars K) (σ.restrictScalars K) x) =
      i (embeddedGaloisRestriction (B := M) i σ x)
    exact (embeddedGaloisRestriction_commutes (B := K) (i.restrictScalars K)
      (σ.restrictScalars K) x).trans (embeddedGaloisRestriction_commutes (B := M) i σ x).symm
  · apply LinearMap.ext
    intro a
    rfl

end GlobalClassFieldTheory.Cohomology

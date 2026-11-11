/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FieldSectionRepresentations
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FieldCoverQuotient

/-!
# Actual Galois cohomology transition maps

For a tower of finite Galois field extensions, geometric restriction of
actual sheaf sections intertwines the two actual Galois actions.
Consequently it gives the finite-stage transition map in every degree
of group cohomology.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale

namespace EtaleCohomology

variable (K L M : Type u) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional K M]
  [IsGalois K L] [IsGalois K M]

/-- The actual etale-site map induced by the inclusion in a field tower. -/
def fieldGaloisEtaleTransition :
    (finiteEtaleInclusion (Spec (.of K))).obj (FiniteEtale.mk (ξ K M)) ⟶
      (finiteEtaleInclusion (Spec (.of K))).obj (FiniteEtale.mk (ξ K L)) :=
  MorphismProperty.Over.homMk (ξ L M) (by
    change Spec.map (CommRingCat.ofHom (algebraMap L M)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K L)) =
        Spec.map (CommRingCat.ofHom (algebraMap K M))
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (IsScalarTower.algebraMap_apply K L M x).symm)

/-- Geometric restriction commutes with restriction of the field
automorphism, as an equality of actual site morphisms. -/
theorem fieldGaloisEtaleTransition_deck (σ : Gal(M/K)) :
    fieldGaloisEtaleTransition K L M ≫
      (finiteEtaleInclusion (Spec (.of K))).map
        (MulOpposite.unop
          (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K L
            (AlgEquiv.restrictNormalHom L σ))).asIso.hom =
    (finiteEtaleInclusion (Spec (.of K))).map
        (MulOpposite.unop
          (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K M σ)).asIso.hom ≫
      fieldGaloisEtaleTransition K L M := by
  apply MorphismProperty.Over.Hom.ext
  change Spec.map (CommRingCat.ofHom (algebraMap L M)) ≫
      Spec.map (CommRingCat.ofHom (AlgEquiv.restrictNormalHom L σ).toRingHom) =
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap L M))
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact AlgEquiv.restrictNormal_commutes σ L x

/-- The actual field-section transition intertwines the actual actions. -/
theorem fieldGaloisSections_transition_action
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (σ : Gal(M/K))
    (s : F.obj.obj (op ((finiteEtaleInclusion (Spec (.of K))).obj
      (FiniteEtale.mk (ξ K L))))) :
    F.obj.map (fieldGaloisEtaleTransition K L M).op
        ((fieldGaloisSheafAction K L F (AlgEquiv.restrictNormalHom L σ)).asIso.hom s) =
      (fieldGaloisSheafAction K M F σ).asIso.hom
        (F.obj.map (fieldGaloisEtaleTransition K L M).op s) := by
  change F.obj.map (fieldGaloisEtaleTransition K L M).op
      (F.obj.map ((finiteEtaleInclusion (Spec (.of K))).map
        (MulOpposite.unop
          (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K L
            (AlgEquiv.restrictNormalHom L σ))).asIso.hom).op s) =
    F.obj.map ((finiteEtaleInclusion (Spec (.of K))).map
      (MulOpposite.unop
        (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv K M σ)).asIso.hom).op
      (F.obj.map (fieldGaloisEtaleTransition K L M).op s)
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp,
    fieldGaloisEtaleTransition_deck, op_comp, F.obj.map_comp]
  rfl

/-- Actual restriction of field sections as an equivariant coefficient map
for the restriction homomorphism on Galois groups. -/
def fieldGaloisSectionsTransitionRepHom
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    Rep.res (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
      (fieldGaloisSheafSectionsRep K L F) ⟶
        fieldGaloisSheafSectionsRep K M F :=
  Rep.ofHom
    ⟨(F.obj.map (fieldGaloisEtaleTransition K L M).op).hom.toIntLinearMap,
      fun σ => by
        apply LinearMap.ext
        intro s
        exact fieldGaloisSections_transition_action K L M F σ s⟩

end EtaleCohomology

namespace EtaleCohomology

/-- The finite-stage cohomology map uses actual geometric coefficient
restriction together with Galois inflation, in every degree. -/
def fieldGaloisCohomologyTransition
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{0}) (n : ℕ) :
    groupCohomology (fieldGaloisSheafSectionsRep K L F) n ⟶
      groupCohomology (fieldGaloisSheafSectionsRep K M F) n :=
  groupCohomology.map (AlgEquiv.restrictNormalHom L)
    (fieldGaloisSectionsTransitionRepHom K L M F) n

end EtaleCohomology

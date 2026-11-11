/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FiniteGaloisCanonicalRefinement
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Exactness of the actual finite Galois section colimit

Canonical finite Galois refinement turns local surjectivity of sheaves
into surjectivity on the section colimit. Left exactness comes from
actual sheaf evaluation and filtered colimits of abelian groups.
Together these prove exactness; it is not a supplied comparison axiom.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry

namespace EtaleCohomology

variable (K : Type u) [Field K]

/-- The functor taking an actual etale sheaf to its finite Galois section colimit. -/
def finiteGaloisSectionColimitFunctor :
    Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf _ _ ⋙
    (Functor.whiskeringLeft
      (FiniteGaloisIntermediateField K (AlgebraicClosure K))
      (Spec (.of K)).Etaleᵒᵖ AddCommGrpCat.{u}).obj
        (finiteGaloisEtaleDiagram K).rightOp ⋙ colim

/-- Actual section colimits are additive in coefficient morphisms. -/
instance finiteGaloisSectionColimitFunctor_additive :
    (finiteGaloisSectionColimitFunctor K).Additive := by
  dsimp only [finiteGaloisSectionColimitFunctor]
  infer_instance

/-- Finite limits commute with this actual filtered section colimit. -/
instance finiteGaloisSectionColimitFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (finiteGaloisSectionColimitFunctor K) := by
  dsimp only [finiteGaloisSectionColimitFunctor]
  infer_instance

/-- The map on section colimits restricts to the actual coefficient map
at every finite Galois stage. -/
theorem finiteGaloisSectionColimitFunctor_map_ι
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}}
    (η : F ⟶ G) (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    finiteGaloisSectionColimitι K F E ≫
        (finiteGaloisSectionColimitFunctor K).map η =
      η.hom.app (op (finiteGaloisEtaleObject K E)) ≫
        finiteGaloisSectionColimitι K G E :=
  colimit.ι_map (Functor.whiskerLeft (finiteGaloisEtaleDiagram K).rightOp η.hom) E

/-- A section at a finite Galois stage lifts through an actual sheaf
epimorphism after a canonical finite Galois inclusion. -/
theorem exists_canonical_finiteGalois_lift_section
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}}
    (η : F ⟶ G) [Epi η]
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))
    (s : G.obj.obj (op (finiteGaloisEtaleObject K E))) :
    ∃ (L : FiniteGaloisIntermediateField K (AlgebraicClosure K)) (h : E ⟶ L)
      (t : F.obj.obj (op (finiteGaloisEtaleObject K L))),
      η.hom.app _ t = G.obj.map ((finiteGaloisEtaleDiagram K).map h.op).op s := by
  have : Sheaf.IsLocallySurjective η :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} η).mpr inferInstance
  obtain ⟨L, h, t, ht⟩ := exists_canonical_finiteGalois_mem_covering_sieve K E
    (Presheaf.imageSieve η.hom s)
    (Presheaf.imageSieve_mem (Spec (.of K)).smallEtaleTopology η.hom s)
  exact ⟨L, h, t, ht⟩

/-- The actual section-colimit functor preserves epimorphisms, by local
lifting and canonical finite Galois refinement. -/
instance finiteGaloisSectionColimitFunctor_preservesEpimorphisms :
    (finiteGaloisSectionColimitFunctor K).PreservesEpimorphisms where
  preserves {F G} η _ := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro x
    obtain ⟨E, s, rfl⟩ := finiteGaloisSectionColimit_exists_stage K G x
    obtain ⟨L, h, t, ht⟩ := exists_canonical_finiteGalois_lift_section K η E s
    refine ⟨finiteGaloisSectionColimitι K F L t, ?_⟩
    have hm := ConcreteCategory.congr_hom
      (finiteGaloisSectionColimitFunctor_map_ι K η L) t
    change (finiteGaloisSectionColimitFunctor K).map η
        (finiteGaloisSectionColimitι K F L t) =
      finiteGaloisSectionColimitι K G L (η.hom.app _ t) at hm
    exact hm.trans ((congrArg (finiteGaloisSectionColimitι K G L) ht).trans
      (ConcreteCategory.congr_hom (finiteGaloisSectionColimitι_transition K G h) s))

/-- Exactness of the actual finite Galois section colimit. -/
instance finiteGaloisSectionColimitFunctor_preservesHomology :
    (finiteGaloisSectionColimitFunctor K).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels
    (finiteGaloisSectionColimitFunctor K)

/-- Finite colimits are preserved by the actual section-colimit functor. -/
instance finiteGaloisSectionColimitFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (finiteGaloisSectionColimitFunctor K) :=
  Functor.preservesFiniteColimits_of_preservesHomology
    (finiteGaloisSectionColimitFunctor K)

/-- Every actual short exact coefficient sequence stays short exact
after passage to the finite Galois section colimit. -/
theorem finiteGaloisSectionColimit_shortExact
    (S : ShortComplex
      (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}))
    (hS : S.ShortExact) :
    (S.map (finiteGaloisSectionColimitFunctor K)).ShortExact :=
  hS.map_of_exact (finiteGaloisSectionColimitFunctor K)

end EtaleCohomology

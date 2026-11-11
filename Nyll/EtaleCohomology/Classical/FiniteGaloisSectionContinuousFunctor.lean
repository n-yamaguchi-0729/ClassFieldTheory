/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FiniteGaloisSectionColimitFunctor
public import Nyll.GaloisCohomology.Topology.ContinuousEquivariantTupleLifting
public import Nyll.ValuedFieldTheory.Valuation.Completion.SeparableClosureAutTopology

/-!
# Continuous geometric-section functors

The actual geometric-section coefficient functor takes values in discrete
topological representations. Its homogeneous continuous cochains are functorial
in the actual etale sheaf.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry

namespace EtaleCohomology

variable (K : Type u) [Field K]

/-- Actual coefficient maps as continuous equivariant maps of geometric sections. -/
def finiteGaloisSectionColimitTopRepMap
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}} (η : F ⟶ G) :
    finiteGaloisSectionColimitTopRep K F ⟶ finiteGaloisSectionColimitTopRep K G := by
  let : TopologicalSpace (finiteGaloisSectionColimit K F) := ⊥
  let : TopologicalSpace (finiteGaloisSectionColimit K G) := ⊥
  have : DiscreteTopology (finiteGaloisSectionColimit K F) := ⟨rfl⟩
  have : DiscreteTopology (finiteGaloisSectionColimit K G) := ⟨rfl⟩
  exact TopRep.ofHom
    ⟨⟨((finiteGaloisSectionColimitFunctor K).map η).hom.toIntLinearMap,
        continuous_of_discreteTopology⟩, fun σ => by
      apply ContinuousLinearMap.ext
      intro x
      exact ConcreteCategory.congr_hom
        (finiteGaloisSectionColimitAction_naturality K η σ) x⟩

/-- The actual geometric-section functor valued in topological representations. -/
def finiteGaloisSectionColimitTopRepFunctor :
    Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
      TopRep.{u} ℤ Gal(AlgebraicClosure K/K) where
  obj := finiteGaloisSectionColimitTopRep K
  map := finiteGaloisSectionColimitTopRepMap K
  map_id F := by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom ((finiteGaloisSectionColimitFunctor K).map_id F) x
  map_comp η θ := by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom ((finiteGaloisSectionColimitFunctor K).map_comp η θ) x

/-- The continuous geometric-section functor is additive. -/
instance finiteGaloisSectionColimitTopRepFunctor_additive :
    (finiteGaloisSectionColimitTopRepFunctor K).Additive where
  map_add := by
    intro F G η θ
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom
      ((finiteGaloisSectionColimitFunctor K).map_add (f := η) (g := θ)) x

/-- Homogeneous continuous cochains of actual geometric sections, as a functor
of the actual etale coefficient sheaf. -/
def finiteGaloisSectionContinuousCochainsFunctor :
    Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
      CochainComplex (TopModuleCat.{u} ℤ) ℕ :=
  finiteGaloisSectionColimitTopRepFunctor K ⋙
    TopRep.homogeneousContinuousCochainsFunctor Gal(AlgebraicClosure K/K)

/-- The actual continuous Galois cohomology functor of geometric sections. -/
def finiteGaloisSectionContinuousCohomologyFunctor (n : ℕ) :
    Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} ⥤ TopModuleCat.{u} ℤ :=
  finiteGaloisSectionContinuousCochainsFunctor K ⋙
    HomologicalComplex.homologyFunctor (TopModuleCat.{u} ℤ) (ComplexShape.up ℕ) n

/-- The continuous cochain functor of geometric sections is additive. -/
instance finiteGaloisSectionContinuousCochainsFunctor_additive :
    (finiteGaloisSectionContinuousCochainsFunctor K).Additive := by
  dsimp only [finiteGaloisSectionContinuousCochainsFunctor]
  infer_instance

/-- Actual sheaf epimorphisms give surjective maps in every degree of the
homogeneous continuous geometric-section complex. -/
theorem finiteGaloisSectionContinuousCochains_map_surjective
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}}
    (η : F ⟶ G) [Epi η] (n : ℕ) :
    Function.Surjective
      (((finiteGaloisSectionContinuousCochainsFunctor K).map η).f n) := by
  have : DiscreteTopology (finiteGaloisSectionColimitTopRep K G) := ⟨rfl⟩
  have hη : Function.Surjective (finiteGaloisSectionColimitTopRepMap K η) :=
    (AddCommGrpCat.epi_iff_surjective ((finiteGaloisSectionColimitFunctor K).map η)).mp
      inferInstance
  have hF : Continuous
      (fun p : Gal(AlgebraicClosure K/K) × finiteGaloisSectionColimitTopRep K F =>
        (finiteGaloisSectionColimitTopRep K F).ρ p.1 p.2) := by
    let : TopologicalSpace (finiteGaloisSectionColimit K F) := ⊥
    have : DiscreteTopology (finiteGaloisSectionColimit K F) := ⟨rfl⟩
    exact finiteGaloisSectionColimitAction_continuous K F
  exact TopRep.homogeneousCochains_map_surjective _ _ _
    (finiteGaloisSectionColimitTopRepMap K η) hη hF n

end EtaleCohomology

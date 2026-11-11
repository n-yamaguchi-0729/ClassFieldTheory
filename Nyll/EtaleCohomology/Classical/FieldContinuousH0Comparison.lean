/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FiniteGaloisSectionContinuousExact
public import Nyll.GaloisCohomology.Topology.ContinuousH0Naturality

/-!
# Natural degree-zero comparison for actual field sections

The actual continuous cohomology in degree zero is naturally actual global
sections. Both the continuous degree-zero isomorphism and geometric descent
are the previously proved maps.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry

namespace EtaleCohomology

variable (K : Type u) [Field K]

/-- The actual degree-zero continuous comparison with geometric invariants
is natural in the etale coefficient sheaf. -/
def finiteGaloisSectionContinuousH0InvariantsNatIso :
    finiteGaloisSectionContinuousCohomologyFunctor K 0 ≅
      finiteGaloisSectionColimitTopRepFunctor K ⋙
        TopRep.invariantsFunctor ℤ Gal(AlgebraicClosure K/K) :=
  NatIso.ofComponents
    (fun F => ContinuousCohomology.zeroIso (finiteGaloisSectionColimitTopRep K F))
    (fun η => ContinuousCohomology.zeroIso_hom_naturality _ _
      (finiteGaloisSectionColimitTopRepMap K η))

/-- Forgetting the topology identifies continuous section invariants
with representation invariants. -/
def finiteGaloisSectionInvariantsUnderlyingIso :
    ((finiteGaloisSectionColimitTopRepFunctor K ⋙
      TopRep.invariantsFunctor ℤ Gal(AlgebraicClosure K/K)) ⋙
      (forget₂ (TopModuleCat.{u} ℤ) (ModuleCat.{u} ℤ) ⋙
        forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})) ≅
    (finiteGaloisSectionColimitRepFunctor K ⋙
      Rep.invariantsFunctor ℤ Gal(AlgebraicClosure K/K) ⋙
        forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- Actual degree-zero continuous Galois cohomology is naturally the actual
global-section functor on the small etale site of the field. -/
def finiteGaloisSectionContinuousH0BaseNatIso :
    (finiteGaloisSectionContinuousCohomologyFunctor K 0 ⋙
      (forget₂ (TopModuleCat.{u} ℤ) (ModuleCat.{u} ℤ) ⋙
        forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})) ≅
    (sheafToPresheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} ⋙
      (evaluation (Spec (.of K)).Etaleᵒᵖ AddCommGrpCat.{u}).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of K)))))) :=
  Functor.isoWhiskerRight (finiteGaloisSectionContinuousH0InvariantsNatIso K) _ ≪≫
    finiteGaloisSectionInvariantsUnderlyingIso K ≪≫
      (finiteGaloisBaseInvariantsNatIso K).symm

/-- Forgetting topology commutes naturally with the actual homology of the
continuous geometric-section complex. -/
def finiteGaloisSectionContinuousModuleHomologyNatIso (n : ℕ) :
    (finiteGaloisSectionContinuousModuleComplexFunctor K ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) n ⋙
        forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}) ≅
    (finiteGaloisSectionContinuousCohomologyFunctor K n ⋙
      (forget₂ (TopModuleCat.{u} ℤ) (ModuleCat.{u} ℤ) ⋙
        forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})) := by
  let U := forget₂ (TopModuleCat.{u} ℤ) (ModuleCat.{u} ℤ)
  let V := forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}
  refine NatIso.ofComponents
    (fun F => V.mapIso
      (ShortComplex.mapHomologyIso
        ((TopRep.homogeneousCochains (finiteGaloisSectionColimitTopRep K F)).sc n) U)) ?_
  intro F G η
  have h := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (TopModuleCat.{u} ℤ)
      (ComplexShape.up ℕ) n).map
        ((finiteGaloisSectionContinuousCochainsFunctor K).map η)) U
  have hm := congrArg V.map h
  change V.map (ShortComplex.homologyMap
      (U.mapShortComplex.map
        ((HomologicalComplex.shortComplexFunctor (TopModuleCat.{u} ℤ)
          (ComplexShape.up ℕ) n).map
            ((finiteGaloisSectionContinuousCochainsFunctor K).map η)))) ≫
      V.map (((TopRep.homogeneousCochains
        (finiteGaloisSectionColimitTopRep K G)).sc n).mapHomologyIso U).hom =
    V.map (((TopRep.homogeneousCochains
      (finiteGaloisSectionColimitTopRep K F)).sc n).mapHomologyIso U).hom ≫
      V.map (U.map (ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor (TopModuleCat.{u} ℤ)
          (ComplexShape.up ℕ) n).map
            ((finiteGaloisSectionContinuousCochainsFunctor K).map η))))
  exact (V.map_comp _ _).symm.trans (hm.trans (V.map_comp _ _))

/-- The module-valued continuous degree-zero cohomology is naturally actual
global sections over the field. -/
def finiteGaloisSectionContinuousModuleH0BaseNatIso :
    (finiteGaloisSectionContinuousModuleComplexFunctor K ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) 0 ⋙
        forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}) ≅
    (sheafToPresheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} ⋙
      (evaluation (Spec (.of K)).Etaleᵒᵖ AddCommGrpCat.{u}).obj
        (op (Scheme.Etale.mk (𝟙 (Spec (.of K)))))) :=
  finiteGaloisSectionContinuousModuleHomologyNatIso K 0 ≪≫
    finiteGaloisSectionContinuousH0BaseNatIso K

end EtaleCohomology

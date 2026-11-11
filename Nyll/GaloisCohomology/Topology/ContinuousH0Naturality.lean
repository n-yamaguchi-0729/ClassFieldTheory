/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Naturality of the actual degree-zero continuous comparison

The existing degree-zero continuous-cohomology isomorphism with invariants
respects coefficient maps. The proof uses the actual cycle inclusion and
evaluation at the identity.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits

namespace ContinuousCohomology

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A B : TopRep.{u} ℤ G)

private def cyclesZeroInvariantsIso :
    cocycles A 0 ≅ A.invariants :=
  cocycles₀Iso A ≪≫ TopModuleCat.ofIso (d₀kerIso A)

private theorem cyclesZeroInvariantsIso_apply (z : cocycles A 0) :
    ((cyclesZeroInvariantsIso A).hom z).val =
      (((TopRep.homogeneousCochains A).iCycles 0) z).val 1 := by
  have hk :
      (cocycles₀Iso A).hom ≫
        TopModuleCat.kerι ((TopRep.homogeneousCochains A).d 0 1) =
      (TopRep.homogeneousCochains A).iCycles 0 := by
    change (KernelFork.ofι ((TopRep.homogeneousCochains A).iCycles 0)
        ((TopRep.homogeneousCochains A).iCycles_d 0 1)).mapOfIsLimit
        (TopModuleCat.isLimitKer _) (𝟙 _) ≫ _ = _
    exact (KernelFork.mapOfIsLimit_ι
      (KernelFork.ofι ((TopRep.homogeneousCochains A).iCycles 0)
        ((TopRep.homogeneousCochains A).iCycles_d 0 1))
      (TopModuleCat.isLimitKer _) (𝟙 _)).trans (Category.comp_id _)
  exact congrArg (fun w : (TopRep.homogeneousCochains A).X 0 => w.val 1)
    (ConcreteCategory.congr_hom hk z)

private theorem cyclesZeroInvariantsIso_naturality (φ : A ⟶ B) :
    cocyclesMap (ContinuousMonoidHom.id G) φ 0 ≫
        (cyclesZeroInvariantsIso B).hom =
      (cyclesZeroInvariantsIso A).hom ≫ (TopRep.invariantsFunctor ℤ G).map φ := by
  apply ConcreteCategory.hom_ext
  intro z
  apply Subtype.ext
  have hc := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i
      (cochainsMap (ContinuousMonoidHom.id G) φ) 0) z
  have hv := congrArg (fun w : (TopRep.homogeneousCochains B).X 0 => w.val 1) hc
  change (((TopRep.homogeneousCochains B).iCycles 0)
      (cocyclesMap (ContinuousMonoidHom.id G) φ 0 z)).val 1 =
    φ.hom ((((TopRep.homogeneousCochains A).iCycles 0) z).val 1) at hv
  exact (cyclesZeroInvariantsIso_apply B _).trans
    (hv.trans (congrArg φ.hom (cyclesZeroInvariantsIso_apply A z).symm))

/-- The actual degree-zero continuous-cohomology isomorphism with invariants
is natural in the coefficient topological representation. -/
theorem zeroIso_hom_naturality (φ : A ⟶ B) :
    map (ContinuousMonoidHom.id G) φ 0 ≫ (zeroIso B).hom =
      (zeroIso A).hom ≫ (TopRep.invariantsFunctor ℤ G).map φ := by
  change HomologicalComplex.homologyMap
      (cochainsMap (ContinuousMonoidHom.id G) φ) 0 ≫
        ((TopRep.homogeneousCochains B).isoHomologyπ₀.inv ≫
          (cyclesZeroInvariantsIso B).hom) =
    ((TopRep.homogeneousCochains A).isoHomologyπ₀.inv ≫
      (cyclesZeroInvariantsIso A).hom) ≫ _
  rw [← Category.assoc, CochainComplex.isoHomologyπ₀_inv_naturality,
    Category.assoc, cyclesZeroInvariantsIso_naturality, Category.assoc]

end ContinuousCohomology

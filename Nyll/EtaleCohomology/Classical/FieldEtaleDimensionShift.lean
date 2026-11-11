/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FieldContinuousH0Comparison
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Actual field cohomology in degree zero and dimension shifting

The base object is terminal in the actual small etale site.
The classical connecting map gives dimension shifting through an actual
injective coefficient sheaf, using the existing derived cohomology sequence.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry

namespace EtaleCohomology

variable (K : Type u) [Field K]

/-- The identity neighborhood is terminal in the actual small etale site. -/
def fieldEtaleIdentityIsTerminal :
    IsTerminal (Scheme.Etale.mk (𝟙 (Spec (.of K)))) :=
  IsTerminal.ofUniqueHom
    (fun Y => MorphismProperty.Over.homMk Y.hom (Category.comp_id _))
    (fun Y f => by
      apply MorphismProperty.Over.Hom.ext
      exact (Category.comp_id f.left).symm.trans f.w)

/-- The actual classical degree-zero field cohomology is actual base sections. -/
def fieldEtaleH0SectionsEquiv
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    Sheaf.H.{u} F 0 ≃+ F.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of K))))) :=
  Sheaf.H.equiv₀ F (fieldEtaleIdentityIsTerminal K)

/-- Classical field cohomology shifts through an actual injective middle
coefficient sheaf by the existing derived connecting homomorphism. -/
def fieldEtaleInjectiveDimensionShift
    (S : ShortComplex (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}))
    (hS : S.ShortExact) [Injective S.X₂] (n : ℕ) :
    Sheaf.H.{u} S.X₃ (n + 1) ≃+ Sheaf.H.{u} S.X₁ (n + 2) :=
  AddEquiv.ofBijective (Sheaf.H.δ hS (n + 1) (n + 2) rfl) (by
    constructor
    · intro x y hxy
      have hd : Sheaf.H.δ hS (n + 1) (n + 2) rfl (x - y) = 0 := by
        rw [map_sub, hxy, sub_self]
      obtain ⟨z, hz⟩ := Sheaf.H.longSequence_exact₃ hS (x - y) rfl hd
      have hz0 : z = 0 := Subsingleton.elim _ _
      rw [hz0, map_zero] at hz
      exact sub_eq_zero.mp hz.symm
    · intro x
      exact Sheaf.H.longSequence_exact₁ hS x (Subsingleton.elim _ _) rfl)

/-- The actual classical connecting map written on actual base sections. -/
def fieldEtaleSectionBoundary
    (S : ShortComplex (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}))
    (hS : S.ShortExact) :
    S.X₃.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of K))))) →+
      Sheaf.H.{u} S.X₁ 1 :=
  (Sheaf.H.δ hS 0 1 rfl).comp
    (fieldEtaleH0SectionsEquiv K S.X₃).symm.toAddMonoidHom

/-- The kernel of the actual section boundary is the image of the actual
coefficient map on base sections. -/
theorem fieldEtaleSectionBoundary_eq_zero_iff
    (S : ShortComplex (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}))
    (hS : S.ShortExact)
    (y : S.X₃.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of K)))))) :
    fieldEtaleSectionBoundary K S hS y = 0 ↔
      ∃ x, S.g.hom.app (op (Scheme.Etale.mk (𝟙 (Spec (.of K))))) x = y := by
  constructor
  · exact Sheaf.H.longSequence_equiv₀_exact₃ hS (fieldEtaleIdentityIsTerminal K) y
  · rintro ⟨x, rfl⟩
    change Sheaf.H.δ hS 0 1 rfl
      ((Sheaf.H.equiv₀ S.X₃ (fieldEtaleIdentityIsTerminal K)).symm
        (S.g.hom.app _ x)) = 0
    rw [← Sheaf.H.equiv₀_symm_naturality (fieldEtaleIdentityIsTerminal K) S.g x]
    have hz :
        AddCommGrpCat.ofHom (Sheaf.H.map S.g 0) ≫
          AddCommGrpCat.ofHom (Sheaf.H.δ hS 0 1 rfl) = 0 :=
      (Sheaf.H.longSequence_exact hS 0 1 rfl).zero 1
    have hx := congrArg
      (fun f : AddCommGrpCat.of (Sheaf.H.{u} S.X₂ 0) ⟶
          AddCommGrpCat.of (Sheaf.H.{u} S.X₁ 1) =>
        f ((Sheaf.H.equiv₀ S.X₂ (fieldEtaleIdentityIsTerminal K)).symm x)) hz
    exact hx

/-- Vanishing of actual H1 of the middle sheaf makes its section boundary
surjective. -/
theorem fieldEtaleSectionBoundary_surjective_of_H1_eq_zero
    (S : ShortComplex (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}))
    (hS : S.ShortExact)
    (hI : ∀ a : Sheaf.H.{u} S.X₂ 1, a = 0) :
    Function.Surjective (fieldEtaleSectionBoundary K S hS) := by
  intro x
  obtain ⟨z, hz⟩ := Sheaf.H.longSequence_exact₁ hS x (hI _) rfl
  refine ⟨fieldEtaleH0SectionsEquiv K S.X₃ z, ?_⟩
  change Sheaf.H.δ hS 0 1 rfl
    ((fieldEtaleH0SectionsEquiv K S.X₃).symm
      (fieldEtaleH0SectionsEquiv K S.X₃ z)) = x
  rw [AddEquiv.symm_apply_apply]
  exact hz

/-- An injective middle coefficient sheaf makes the actual section boundary
surjective onto actual classical first cohomology. -/
theorem fieldEtaleSectionBoundary_surjective
    (S : ShortComplex (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}))
    (hS : S.ShortExact) [Injective S.X₂] :
    Function.Surjective (fieldEtaleSectionBoundary K S hS) :=
  fieldEtaleSectionBoundary_surjective_of_H1_eq_zero K S hS
    (fun a => Subsingleton.elim a 0)

/-- Actual first field cohomology is the section cokernel when the middle
sheaf has vanishing H1. -/
def fieldEtaleH1CokernelIso_of_H1_eq_zero
    (S : ShortComplex (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}))
    (hS : S.ShortExact)
    (hI : ∀ a : Sheaf.H.{u} S.X₂ 1, a = 0) :
    cokernel (S.g.hom.app (op (Scheme.Etale.mk (𝟙 (Spec (.of K)))))) ≅
      AddCommGrpCat.of (Sheaf.H.{u} S.X₁ 1) := by
  let f := S.g.hom.app (op (Scheme.Etale.mk (𝟙 (Spec (.of K)))))
  let g : S.X₃.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of K))))) ⟶
      AddCommGrpCat.of (Sheaf.H.{u} S.X₁ 1) :=
    AddCommGrpCat.ofHom (fieldEtaleSectionBoundary K S hS)
  have hfg : f ≫ g = 0 := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (fieldEtaleSectionBoundary_eq_zero_iff K S hS (f x)).mpr ⟨x, rfl⟩
  let T := ShortComplex.mk f g hfg
  have hT : T.Exact := (ShortComplex.ab_exact_iff T).mpr
    (fun y hy => (fieldEtaleSectionBoundary_eq_zero_iff K S hS y).mp hy)
  have : Epi g :=
    (AddCommGrpCat.epi_iff_surjective g).mpr
      (fieldEtaleSectionBoundary_surjective_of_H1_eq_zero K S hS hI)
  exact (cokernelIsCokernel f).coconePointUniqueUpToIso hT.gIsCokernel

/-- Actual classical first field cohomology is the cokernel of base sections
of an actual coefficient sequence with injective middle sheaf. -/
def fieldEtaleH1CokernelIso
    (S : ShortComplex (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}))
    (hS : S.ShortExact) [Injective S.X₂] :
    cokernel (S.g.hom.app (op (Scheme.Etale.mk (𝟙 (Spec (.of K)))))) ≅
      AddCommGrpCat.of (Sheaf.H.{u} S.X₁ 1) :=
  fieldEtaleH1CokernelIso_of_H1_eq_zero K S hS
    (fun a => Subsingleton.elim a 0)

/-- Actual continuous first field cohomology is the same cokernel of actual
base sections of an injective coefficient presentation. -/
def fieldContinuousH1CokernelIso
    (S : ShortComplex (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}))
    (hS : S.ShortExact) [Injective S.X₂] :
    cokernel (S.g.hom.app (op (Scheme.Etale.mk (𝟙 (Spec (.of K)))))) ≅
      (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).obj
        (((finiteGaloisSectionContinuousModuleComplexFunctor K).obj S.X₁).homology 1) := by
  let T := S.map (finiteGaloisSectionContinuousModuleComplexFunctor K)
  have hT : T.ShortExact := finiteGaloisSectionContinuousModuleComplex_shortExact K S hS
  let U := forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}
  let δ := hT.δ 0 1 rfl
  let E := ShortComplex.mk (HomologicalComplex.homologyMap T.g 0) δ (hT.comp_δ 0 1 rfl)
  have hE : E.Exact := hT.homology_exact₃ 0 1 rfl
  have : Epi δ := hT.epi_δ 0 1 rfl
    (finiteGaloisSectionContinuousModuleComplex_injective_isZero K S.X₂ 0)
  have hEA : (E.map U).Exact := hE.map U
  have : Epi (E.map U).g := by
    change Epi (U.map δ)
    infer_instance
  let f := U.map (HomologicalComplex.homologyMap T.g 0)
  let e : cokernel f ≅ U.obj (T.X₁.homology 1) :=
    (cokernelIsCokernel f).coconePointUniqueUpToIso hEA.gIsCokernel
  let e₀ := finiteGaloisSectionContinuousModuleH0BaseNatIso K
  let g := S.g.hom.app (op (Scheme.Etale.mk (𝟙 (Spec (.of K)))))
  have hn : f ≫ (e₀.app S.X₃).hom = (e₀.app S.X₂).hom ≫ g :=
    e₀.hom.naturality S.g
  exact (cokernel.mapIso (f := f) g (e₀.app S.X₂) (e₀.app S.X₃) hn).symm ≪≫ e

/-- Actual classical first field cohomology and actual continuous cohomology
of geometric sections agree, by an actual injective presentation. -/
def fieldEtaleContinuousModuleH1Equiv
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    Sheaf.H.{u} F 1 ≃+
      (((finiteGaloisSectionContinuousModuleComplexFunctor K).obj F).homology 1) := by
  let i := Injective.ι F
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
  exact ((fieldEtaleH1CokernelIso K S hS).symm ≪≫
    fieldContinuousH1CokernelIso K S hS).addCommGroupIsoToAddEquiv

/-- Objectwise comparison of actual classical field cohomology with the
homology of the actual continuous geometric-section complex in every degree.
It is constructed from the natural degree-zero comparison and the proved
injective acyclicity on both sides; no higher comparison premise is assumed. -/
def fieldEtaleContinuousModuleEquiv :
    (n : ℕ) →
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) →
    Sheaf.H.{u} F n ≃+
      (((finiteGaloisSectionContinuousModuleComplexFunctor K).obj F).homology n)
  | 0, F =>
      (fieldEtaleH0SectionsEquiv K F).trans
        (((finiteGaloisSectionContinuousModuleH0BaseNatIso K).app F).symm.addCommGroupIsoToAddEquiv)
  | 1, F => fieldEtaleContinuousModuleH1Equiv K F
  | n + 2, F => by
      let i := Injective.ι F
      let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
      let e := (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).mapIso
        (finiteGaloisSectionContinuousDimensionShift K S hS n)
      exact (fieldEtaleInjectiveDimensionShift K S hS n).symm.trans
        ((fieldEtaleContinuousModuleEquiv (n + 1) S.X₃).trans
          e.addCommGroupIsoToAddEquiv)

/-- Actual derived etale cohomology of an arbitrary field agrees
objectwise, in every degree, with actual continuous absolute Galois cohomology
of its geometric sections. No naturality in higher degrees is asserted here. -/
def fieldEtaleContinuousCohomologyEquiv
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{u} F n ≃+
      continuousCohomology n (finiteGaloisSectionColimitTopRep K F) :=
  (fieldEtaleContinuousModuleEquiv K n F).trans
    (((finiteGaloisSectionContinuousModuleHomologyNatIso K n).app F).addCommGroupIsoToAddEquiv)

end EtaleCohomology

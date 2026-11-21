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

/-- Degree-zero cocycles identify with the original invariant coefficients. -/
def cyclesZeroInvariantsIso :
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

/-- Degree-zero comparison evaluates the original cocycle at the identity. -/
theorem zeroIso_hom_π_val (z : cocycles A 0) :
    ((zeroIso A).hom (π A 0 z)).val =
      ((TopRep.homogeneousCochains A).iCycles 0 z).val 1 := by
  let C := TopRep.homogeneousCochains A
  change ((cyclesZeroInvariantsIso A).hom
    (C.isoHomologyπ₀.inv (C.isoHomologyπ₀.hom z))).val = _
  rw [Iso.hom_inv_id_apply]
  exact cyclesZeroInvariantsIso_apply A z

/-- The degree-zero cocycle for a fixed coefficient uses the constant
function on the acting group. -/
def fixedCocycleZero (a : A.invariants) : cocycles A 0 :=
  (cyclesZeroInvariantsIso A).inv a

theorem fixedCocycleZero_apply (a : A.invariants) (g : G) :
    (((TopRep.homogeneousCochains A).iCycles 0) (fixedCocycleZero A a)).val g = a.val := by
  let C := TopRep.homogeneousCochains A
  let z := fixedCocycleZero A a
  have h₁ : (C.iCycles 0 z).val 1 = a.val := by
    rw [← cyclesZeroInvariantsIso_apply A z]
    have h : (cyclesZeroInvariantsIso A).hom ((cyclesZeroInvariantsIso A).inv a) = a :=
      Iso.inv_hom_id_apply (cyclesZeroInvariantsIso A) a
    exact congrArg (fun x : A.invariants => x.val) h
  have h := congrArg (fun w : C.X 1 => w.val 1 g)
    (ConcreteCategory.congr_hom (C.iCycles_d 0 1) z)
  change ((C.d 0 1) (C.iCycles 0 z)).val 1 g = 0 at h
  rw [congrArg (fun w => w 1 g) (TopRep.homogeneousCochains.d_apply A 0 (C.iCycles 0 z))] at h
  change (C.iCycles 0 z).val g - (C.iCycles 0 z).val 1 = 0 at h
  exact (sub_eq_zero.mp h).trans h₁

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

/-- A degree-zero cocycle is the constant cochain with the invariant value
represented by its cohomology class. -/
theorem zeroIso_hom_π_apply (z : cocycles A 0) (a : G) :
    ((zeroIso A).hom (π A 0 z)).val = ((TopRep.homogeneousCochains A).iCycles 0 z).val a := by
  let C := TopRep.homogeneousCochains A
  let v := C.iCycles 0 z
  have hOne : ((zeroIso A).hom (π A 0 z)).val = v.val 1 := zeroIso_hom_π_val A z
  have h := congrArg (fun w : C.X 1 => w.val 1 a)
    (ConcreteCategory.congr_hom (C.iCycles_d 0 1) z)
  have hd := congrArg (fun w => w 1 a) (TopRep.homogeneousCochains.d_apply A 0 v)
  change (C.d 0 1 v).val 1 a = 0 at h
  rw [hd] at h
  change v.val a - v.val 1 = 0 at h
  exact hOne.trans (sub_eq_zero.mp h).symm

end ContinuousCohomology

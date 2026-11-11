/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FiniteGaloisSectionColimit
public import Nyll.EtaleCohomology.Classical.FieldGaloisTransitions

/-!
# Absolute Galois action on actual section colimits

The finite-stage actions commute with actual restriction along field
inclusions. They therefore induce an action of the absolute Galois group
on the actual filtered colimit, with its prescribed action on every stage.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry

namespace EtaleCohomology

variable (K : Type u) [Field K]
variable (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})

/-- Absolute Galois automorphisms act compatibly on actual finite-stage sections. -/
theorem finiteGaloisSectionDiagram_action_naturality
    (σ : Gal(AlgebraicClosure K/K))
    {E L : FiniteGaloisIntermediateField K (AlgebraicClosure K)} (h : E ⟶ L) :
    (finiteGaloisSectionDiagram K F).map h ≫
        (fieldGaloisSheafAction K L F (AlgEquiv.restrictNormalHom L σ)).asIso.hom =
      (fieldGaloisSheafAction K E F (AlgEquiv.restrictNormalHom E σ)).asIso.hom ≫
        (finiteGaloisSectionDiagram K F).map h := by
  let : Algebra E L := (IntermediateField.inclusion h.le).toRingHom.toAlgebra
  have : IsScalarTower K E L :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      ((IntermediateField.inclusion h.le).commutes x).symm)
  have : IsScalarTower E L (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hr : AlgEquiv.restrictNormalHom E (AlgEquiv.restrictNormalHom L σ) =
      AlgEquiv.restrictNormalHom E σ :=
    (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E L σ).symm
  apply ConcreteCategory.hom_ext
  intro s
  change (fieldGaloisSheafAction K L F (AlgEquiv.restrictNormalHom L σ)).asIso.hom
      (F.obj.map (fieldGaloisEtaleTransition K E L).op s) =
    F.obj.map (fieldGaloisEtaleTransition K E L).op
      ((fieldGaloisSheafAction K E F (AlgEquiv.restrictNormalHom E σ)).asIso.hom s)
  rw [← hr]
  exact (fieldGaloisSections_transition_action K E L F
    (AlgEquiv.restrictNormalHom L σ) s).symm

/-- The absolute Galois action as automorphisms of the actual section diagram. -/
def finiteGaloisSectionDiagramAction :
    Gal(AlgebraicClosure K/K) →* Aut (finiteGaloisSectionDiagram K F) where
  toFun σ := Aut.of <| NatIso.ofComponents
    (fun E : FiniteGaloisIntermediateField K (AlgebraicClosure K) =>
      (fieldGaloisSheafAction K E F (AlgEquiv.restrictNormalHom E σ)).asIso)
    (fun h => finiteGaloisSectionDiagram_action_naturality K F σ h)
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply NatTrans.ext
    funext E
    change (fieldGaloisSheafAction K E F (AlgEquiv.restrictNormalHom E 1)).asIso.hom = 𝟙 _
    rw [map_one, map_one]
    rfl
  map_mul' σ τ := by
    apply Aut.ext
    apply Iso.ext
    apply NatTrans.ext
    funext E
    change (fieldGaloisSheafAction K E F
      (AlgEquiv.restrictNormalHom E (σ * τ))).asIso.hom =
      (fieldGaloisSheafAction K E F (AlgEquiv.restrictNormalHom E τ)).asIso.hom ≫
        (fieldGaloisSheafAction K E F (AlgEquiv.restrictNormalHom E σ)).asIso.hom
    rw [map_mul, map_mul]
    rfl

/-- The absolute Galois action induced on the actual finite-stage section colimit. -/
def finiteGaloisSectionColimitAction :
    Gal(AlgebraicClosure K/K) →* Aut (finiteGaloisSectionColimit K F) :=
  (Functor.mapAut (finiteGaloisSectionDiagram K F) colim).comp
    (finiteGaloisSectionDiagramAction K F)

/-- The colimit action agrees with the actual field action at every finite stage. -/
theorem finiteGaloisSectionColimitAction_ι
    (σ : Gal(AlgebraicClosure K/K))
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    finiteGaloisSectionColimitι K F E ≫
        (finiteGaloisSectionColimitAction K F σ).asIso.hom =
      (fieldGaloisSheafAction K E F (AlgEquiv.restrictNormalHom E σ)).asIso.hom ≫
        finiteGaloisSectionColimitι K F E :=
  colimit.ι_map (finiteGaloisSectionDiagramAction K F σ).asIso.hom E

/-- Actual geometric sections form an integer-linear absolute Galois representation. -/
def finiteGaloisSectionColimitRep : Rep.{u} ℤ Gal(AlgebraicClosure K/K) :=
  Rep.of
    { toFun := fun σ => ((finiteGaloisSectionColimitAction K F σ).asIso.hom).hom.toIntLinearMap
      map_one' := by
        apply LinearMap.ext
        intro s
        change (finiteGaloisSectionColimitAction K F 1).asIso.hom s = s
        rw [map_one]
        rfl
      map_mul' σ τ := by
        apply LinearMap.ext
        intro s
        exact congrArg (fun a => a.asIso.hom s)
          (map_mul (finiteGaloisSectionColimitAction K F) σ τ) }

end EtaleCohomology

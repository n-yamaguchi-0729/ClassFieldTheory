/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_baseChange_points_mul_poincare_compat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Representation
public import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
public import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicEquivalence.AlgEquivZeroCut
public import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicEquivalence.AlgEquivZeroGroupCut
public import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Basic
public import Nyll.SchemeTheory.BaseChange.Points
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.RelativeGroupLawGrpObj
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
public import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange
public import Nyll.AlgebraicCurves.Geometry.Picard.BaseChange.RelativePic0DesignationBaseChange
public import Nyll.AlgebraicCurves.Geometry.Picard.Poincare.PicardRepresentabilityPoincarePullbackMulIso

public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.RepresentsRelSubPicPresheaf
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.RepresentsRelSubPicGroup
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.RepresentsRelSubPicBaseChange

/-!
# Base change of Picard points and the Poincare bundle

Compare points, multiplication, and the Poincare bundle after changing the base ring.
-/
@[expose] public section

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.BaseChange_points_mul_poincare_compat

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.RelPicard.BaseChange

open scoped CategoryTheory.MonObj

theorem _root_.AlgebraicGeometry.RelPicard.baseChange_points_mul_poincare_compat
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L)) :
    let : GrpObj (Over.mk (D.baseChange R').toBase) :=
      (show RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)).toSubPicCondition
        (D.baseChange R') from h').grpObj
    ∃ Θ : (Over.mk (𝟙 (Spec (CommRingCat.of R'))) ⟶ Over.mk (D.baseChange R').toBase) ≃
        SchemeHomOver (specMap R R') D.toBase,
      (∀ a, (Θ a).1 = a.left ≫ pullback.fst D.toBase (specMap R R')) ∧
      (∀ a b, Θ (a * b) =
        (show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D
            from h).relativeGroupLaw.mul
          (specMap R R') (Θ a) (Θ b)) ∧
      ∀ a, Nonempty ((h.poincare.pullbackAlong (Θ a)).L ≅
        (Scheme.Modules.pullback (BaseChange.κ c R' (𝟙 (Spec (CommRingCat.of R')))).inv).obj
          (h'.poincare.pullbackAlong
            (⟨a.left, Over.w a⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R')))
                (D.baseChange R').toBase)).L) := by
  classical
  intro baseChangeGroup
  let ψ₀ : SchemeHomOver ((D.baseChange R').toBase ≫ specMap R R') D.toBase :=
    ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩
  let P' : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε)
      (D.baseChange R').toBase :=
    ofR c ε R' (h.poincare.pullbackAlong ψ₀)
  have chain : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R')}
      (g' : SchemeHomOver t (D.baseChange R').toBase),
      (toR c ε R' (P'.pullbackAlong g')).L
          ≅ (h.poincare.pullbackAlong (postComp ψ₀ (overR R' g'))).L :=
    fun g' => (toR_pullbackAlong_iso c ε R' g' P').symm ≪≫
      (Scheme.Modules.pullback (baseChangeSnd c (overR R' g'))).mapIso (toR_ofR_iso c ε R' _) ≪≫
      h.poincare.pullbackAlongPullbackAlongIso ψ₀ (overR R' g')
  let t := 𝟙 (Spec (CommRingCat.of R'))
  let baseMap := specMap R R'
  let pt := (schemeHomOverEquivOverHom t (D.baseChange R').toBase).symm
  let adjustBase : SchemeHomOver (t ≫ baseMap) D.toBase ≃ SchemeHomOver baseMap D.toBase :=
    { toFun := SchemeHomOver.castBase (Category.id_comp baseMap)
      invFun := SchemeHomOver.castBase (Category.id_comp baseMap).symm
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  let changePoint := pt.trans
    ((GoodReductionJacobian.RelativeGroupLaw.baseChangePointEquiv baseMap (f := D.toBase) t).trans
      adjustBase)
  have poinc : ∀ a : Over.mk (𝟙 (Spec (CommRingCat.of R'))) ⟶ Over.mk (D.baseChange R').toBase,
      (toR c ε R' (h'.poincare.pullbackAlong (pt a))).L
          ≅ (h.poincare.pullbackAlong (changePoint a)).L :=
    fun a =>
      (Scheme.Modules.pullback (κ c R' (𝟙 (Spec (CommRingCat.of R')))).inv).mapIso
          ((Scheme.Modules.pullback (baseChangeSnd (baseChange R c R') (pt a))).mapIso hP.some) ≪≫
        chain (pt a) ≪≫
        (Iso.refl _ : (h.poincare.pullbackAlong (postComp ψ₀ (overR R' (pt a)))).L ≅
          (h.poincare.pullbackAlong (changePoint a)).L)
  refine ⟨changePoint, fun a => rfl, fun a b => ?_, fun a => ⟨(poinc a).symm⟩⟩
  obtain ⟨i₁⟩ := (show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D
      from h)
    |>.nonempty_poincare_pullbackAlong_mul_iso (T := Over.mk (specMap R R'))
      (schemeHomOverToOverHom (changePoint a)) (schemeHomOverToOverHom (changePoint b))
  obtain ⟨i₂⟩ := (show RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)).toSubPicCondition
        (D.baseChange R') from h')
    |>.nonempty_poincare_pullbackAlong_mul_iso (T := Over.mk (𝟙 (Spec (CommRingCat.of R')))) a b
  refine h.ext_of_iso (specMap R R') _ _ ⟨?_⟩
  exact (poinc (a * b)).symm ≪≫
    (Scheme.Modules.pullback (κ c R' (𝟙 (Spec (CommRingCat.of R')))).inv).mapIso i₂ ≪≫
    Scheme.Modules.pullbackTensorObjIso (κ c R' (𝟙 (Spec (CommRingCat.of R')))).inv _ _ ≪≫
    (poinc a ⊗ᵢ poinc b) ≪≫ i₁.symm
end JacobianVarieties.Picard.Proofs.BaseChange_points_mul_poincare_compat
end ProofImplementation

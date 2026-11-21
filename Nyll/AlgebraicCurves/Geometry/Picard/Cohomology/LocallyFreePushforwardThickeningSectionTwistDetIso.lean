/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_thickening_sectionTwist_and_nonempty_det_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.Util.WithWeakNamespace
public import Nyll.AlgebraicCurves.Geometry.Picard.Cohomology.ShortExactMapPushforwardThickening
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.IdealSheafModule
public import Nyll.AlgebraicCurves.Geometry.Picard.Theta.ThetaBundle
public import Nyll.SchemeTheory.Modules.LocallyFreeOfRank
public import Nyll.SchemeTheory.Modules.ExteriorPower.Det
public import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
public import Nyll.SchemeTheory.Modules.Functoriality.BaseChangeHom
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.Cartier
public import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.HomFiniteFinrankSubschemeIotaKerPow
public import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.HomInvertibleKerCompEqId
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealPow
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealInvertibleInvModule
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealInvertibleModule
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleTensor
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleDual
public import Nyll.SchemeTheory.Modules.Invertible.RankOne
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Determinants.DetSuccIsoDetTensor
public import Nyll.SchemeTheory.Modules.ExteriorPower.ExteriorPowerLocal
public import Nyll.SchemeTheory.Modules.Exactness
public import Nyll.SchemeTheory.Modules.Functoriality.LocallyFreePushforwardFinite
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealShortExactThickeningUnit
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealEpiUnitAppTensorInvModulePowShortExact
public import Nyll.AlgebraicCurves.Geometry.Picard.Cohomology.PullbackSectionTwistIso
public import Nyll.SchemeTheory.Modules.Functoriality.PullbackUnitComposition
public import Nyll.SchemeTheory.Modules.OpenImmersionUnit

/-!
# Sections on an infinitesimal thickening of a curve section

This file studies a rigidified line bundle, tensored with a section twist, on the infinitesimal
thickenings of a section of a proper smooth relative curve. Its pushforward is locally free of
the thickness rank, and its determinant is isomorphic to the unit sheaf.
-/

@[expose] public section

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs
namespace IsLocallyFreeOfRank_pushforward_thickening_sectionTwist_and_nonempty_det_iso
attribute [-instance]
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
  TwoChartCech.Sections.M0_moduleA
  TwoChartCech.Sections.M1_module
  TwoChartCech.Cover.A01_algebra
  TwoChartCech.Cover.A0_algebra
  TwoChartCech.Cover.A1_commRing
  TwoChartCech.Cover.A1_algebra
  TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup
  TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup
  TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower
  TwoChartCech.Sections.M01_moduleA
  TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA
  TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing
  TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module
  CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free
  CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite
  CoherentBaseChange.TwoTermComplex.C1_free
  SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp
  AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I
  AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq
  PresheafOfModules.pushforwardCongr_inv_app_app_apply
  PresheafOfModules.pushforwardNatTrans_app_app_apply
  PresheafOfModules.pushforwardCongr_hom_app_app_apply
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0
  TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq
  TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec
  TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply
  TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply
  CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply
  SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite
open _root_.TopologicalSpace
open _root_.TensorProduct

namespace Ws31ThetaF

open AlgebraicGeometry.Scheme.Modules
open JacobianVarieties.Picard.Proofs.ShortExact_map_pushforward_thickening.Ws31ThetaF
open JacobianVarieties.Picard.Proofs.ShortExact_map_pushforward_thickening.Ws31ThetaF.E6
  (nonempty_pullback_rigSection_module_iso nonempty_pushforward_thickening_one_iso
    nonempty_pullback_rigSection_G_iso)

section setting2

variable (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
  [IsProper c] [SmoothOfRelativeDimension 1 c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))

omit [IsProper c] [SmoothOfRelativeDimension 1 c] in
private theorem thickening_zero (H : (pullback c t).Modules) :
    IsLocallyFreeOfRank 0 (Fm k c ε t 0 H) ∧
      Nonempty (Scheme.Modules.det 0 (Fm k c ε t 0 H) ≅ 𝟙_ T.Modules) := by
  have : IsEmpty ((sectionIdeal c ε t ^ 0).subscheme) :=
    BaseCase.isEmpty_subscheme_of_support_eq_bot _ (BaseCase.support_pow_zero _)
  have hZ : IsZero (Fm k c ε t 0 H) :=
    (Scheme.Modules.pushforward (pullback.snd c t)).map_isZero
      ((Scheme.Modules.pushforward ((sectionIdeal c ε t ^ 0).subschemeι)).map_isZero
        (BaseCase.isZero_of_isEmpty _))
  exact ⟨BaseCase.isLocallyFreeOfRank_zero_of_isZero hZ,
    BaseCase.nonempty_det_zero_iso_of_isZero hZ⟩


theorem step [LocallyOfFiniteType t] :
    ∀ m : ℕ, ∀ (H : (pullback c t).Modules), IsInvertible H →
      Nonempty ((Scheme.Modules.pullback (rigSection c t ε)).obj H ≅ 𝟙_ T.Modules) →
      IsLocallyFreeOfRank m (Fm k c ε t m H) ∧
        Nonempty (Scheme.Modules.det m (Fm k c ε t m H) ≅ 𝟙_ T.Modules) := by
  intro m
  induction m with
  | zero => intro H _ _; exact thickening_zero k c ε t H
  | succ m ih =>
    intro H hH hσH
    have h𝓘 := isInvertible_sectionIdeal k c ε t
    have hH' : IsInvertible (H ⊗ (sectionIdeal c ε t).module) := hH.tensor h𝓘.isInvertible_module
    have hσH' : Nonempty ((Scheme.Modules.pullback (rigSection c t ε)).obj
      (H ⊗ (sectionIdeal c ε t).module) ≅
        𝟙_ T.Modules) := by
      obtain ⟨a⟩ := hσH
      obtain ⟨b⟩ := nonempty_pullback_rigSection_module_iso k c ε t
      exact ⟨pullbackTensorObjIso (rigSection c t ε) H _ ≪≫ (a ⊗ᵢ b) ≪≫ λ_ _⟩
    obtain ⟨ih1, ⟨ihdet⟩⟩ := ih _ hH' hσH'
    obtain ⟨S, hS, ⟨e₁⟩, e₂, e₃, hpin⟩ :=
      Scheme.IdealSheafData.IsInvertible.exists_shortExact_thickening_unit h𝓘 H hH m
    have hS' := AlgebraicGeometry.RelPicard.shortExact_map_pushforward_thickening
      k c ε t H hH m S hS e₂ e₃ hpin
    have h₂ :
        IsLocallyFreeOfRank (m + 1) (S.map (Scheme.Modules.pushforward (pullback.snd c t))).X₂ :=
      IsLocallyFreeOfRank.of_iso ((Scheme.Modules.pushforward (pullback.snd c t)).mapIso e₂).symm
        (lf_gen k c ε t H hH (m + 1) (Nat.succ_ne_zero m))
    have h₁ : IsLocallyFreeOfRank m (S.map (Scheme.Modules.pushforward (pullback.snd c t))).X₁ :=
      IsLocallyFreeOfRank.of_iso
        ((Scheme.Modules.pushforward (pullback.snd c t)).mapIso e₁).symm ih1
    obtain ⟨e₃'⟩ := nonempty_pushforward_thickening_one_iso k c ε t H
    obtain ⟨a⟩ := hσH
    let e3 : (S.map (Scheme.Modules.pushforward (pullback.snd c t))).X₃ ≅ 𝟙_ T.Modules :=
      (Scheme.Modules.pushforward (pullback.snd c t)).mapIso e₃ ≪≫ e₃' ≪≫ a
    have h₃ : IsInvertible (S.map (Scheme.Modules.pushforward (pullback.snd c t))).X₃ :=
      (isLocallyFreeOfRank_one_iff_isInvertible _).mp
        (IsLocallyFreeOfRank.of_iso e3.symm
          ((isLocallyFreeOfRank_one_iff_isInvertible _).mpr (isInvertible_unit T)))
    obtain ⟨edet⟩ := nonempty_det_succ_iso_det_tensor_of_shortExact _ hS' h₁ h₂ h₃
    refine ⟨IsLocallyFreeOfRank.of_iso
      ((Scheme.Modules.pushforward (pullback.snd c t)).mapIso e₂) h₂, ⟨?_⟩⟩
    exact ((Scheme.Modules.exteriorPower T (m + 1)).mapIso
        ((Scheme.Modules.pushforward (pullback.snd c t)).mapIso e₂)).symm ≪≫ edet ≪≫
      (((Scheme.Modules.exteriorPower T m).mapIso
          ((Scheme.Modules.pushforward (pullback.snd c t)).mapIso e₁) ≪≫ ihdet) ⊗ᵢ e3) ≪≫ λ_ _

theorem thetaF [LocallyOfFiniteType t] (M : RigidifiedLineBundle c ε t) (r n : ℕ) :
    IsLocallyFreeOfRank n (Fm k c ε t n (M.L ⊗ sectionTwist c ε t r)) ∧
      Nonempty (Scheme.Modules.det n (Fm k c ε t n (M.L ⊗ sectionTwist c ε t r)) ≅ 𝟙_ T.Modules) :=
  step k c ε t n _ (isInvertible_G k c ε t M r)
    (nonempty_pullback_rigSection_G_iso k c ε t M r)

end setting2

end Ws31ThetaF

with_weak_namespace _root_.JacobianVarieties.Picard.Proofs
open IsLocallyFreeOfRank_pushforward_thickening_sectionTwist_and_nonempty_det_iso.Ws31ThetaF in
with_weak_namespace _root_.AlgebraicGeometry.RelPicard
theorem isLocallyFreeOfRank_pushforward_thickening_sectionTwist_and_nonempty_det_iso
    (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType t]
    (M : RigidifiedLineBundle c ε t) (r n : ℕ) :
    Scheme.Modules.IsLocallyFreeOfRank n
        ((Scheme.Modules.pushforward (pullback.snd c t)).obj
          ((Scheme.Modules.pushforward ((sectionIdeal c ε t ^ n).subschemeι)).obj
            ((Scheme.Modules.pullback ((sectionIdeal c ε t ^ n).subschemeι)).obj
              (M.L ⊗ sectionTwist c ε t r)))) ∧
      Nonempty (Scheme.Modules.det n
          ((Scheme.Modules.pushforward (pullback.snd c t)).obj
            ((Scheme.Modules.pushforward ((sectionIdeal c ε t ^ n).subschemeι)).obj
              ((Scheme.Modules.pullback ((sectionIdeal c ε t ^ n).subschemeι)).obj
                (M.L ⊗ sectionTwist c ε t r))))
        ≅ 𝟙_ T.Modules) :=
  thetaF k c ε t M r n
end IsLocallyFreeOfRank_pushforward_thickening_sectionTwist_and_nonempty_det_iso
end JacobianVarieties.Picard.Proofs
end ProofImplementation

open _root_.PresheafOfModules.PullbackMonoidal
  _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
  TwoChartCech.Sections.M0_moduleA
  TwoChartCech.Sections.M1_module
  TwoChartCech.Cover.A01_algebra
  TwoChartCech.Cover.A0_algebra
  TwoChartCech.Cover.A1_commRing
  TwoChartCech.Cover.A1_algebra
  TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup
  TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup
attribute [-instance]
  TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower
  TwoChartCech.Sections.M01_moduleA
  TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA
  TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing
  TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module
  CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free
  CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite
  CoherentBaseChange.TwoTermComplex.C1_free
  SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app
  AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp
  AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I
  AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq
  exteriorPower.mulₗ_apply_coe
  PresheafOfModules.pushforwardCongr_inv_app_app_apply
  PresheafOfModules.pushforwardNatTrans_app_app_apply
  PresheafOfModules.pushforwardCongr_hom_app_app_apply
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
attribute [-simp]
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0
  TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq
  TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec
  TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply
  TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply
  CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply
  SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply

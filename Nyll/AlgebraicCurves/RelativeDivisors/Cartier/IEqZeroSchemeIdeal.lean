/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Sheaves.IdealSheafComap
public import Nyll.SchemeTheory.RingTheory.PushoutKernel

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.IsTensorProduct
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.SectionZeroScheme
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.IdealSheafModule
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.RelEffCartierDiv
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.Cartier
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleInvertibleZeroSchemeIdealFlat
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIsoInvModuleZeroSchemeIdeal
public import Nyll.AlgebraicCurves.RelativeDivisors.LineBundles.InvertibleI

/-!
Construct the effective relative Cartier divisor cut out by a section of an invertible sheaf,
and compute its ideal after base change.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  SheafOfModules.isIso_ihomModelToIhom
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
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
attribute [-simp]
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
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry hiding Scheme.IdealSheafData.ideal_comap_of_le
open _root_.TensorProduct
open _root_.nonZeroDivisors

namespace Algebra
open _root_.Algebra
namespace IsPushout
open _root_.Algebra.IsPushout
open _root_.Algebra.IsPushout
open _root_.Algebra

theorem ker_algebraMap_eq_map_ker
    (R B C P : Type*) [CommRing R] [CommRing B] [CommRing C] [CommRing P]
    [Algebra R B] [Algebra R C] [Algebra B P] [Algebra C P] [Algebra R P]
    [IsScalarTower R B P] [IsScalarTower R C P] [Algebra.IsPushout R B C P]
    (hC : Function.Surjective (algebraMap R C)) :
    RingHom.ker (algebraMap B P) = (RingHom.ker (algebraMap R C)).map (algebraMap R B) := by
  exact _root_.Algebra.IsPushout.ker_algebraMap_eq_map_ker R B C P hC

end Algebra.IsPushout

namespace CommRingCat
open _root_.CommRingCat
open _root_.CommRingCat

theorem ker_eq_map_ker_of_isPushout {R B C P : CommRingCat.{u}} {f : R ⟶ B} {g : R ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P} (h : IsPushout f g inl inr)
    (hg : Function.Surjective g.hom) :
    RingHom.ker inl.hom = (RingHom.ker g.hom).map f.hom := by
  exact _root_.CommRingCat.ker_eq_map_ker_of_isPushout h hg

end CommRingCat

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace IdealSheafData
open _root_.AlgebraicGeometry.Scheme.IdealSheafData
open _root_.AlgebraicGeometry.Scheme.IdealSheafData hiding ideal_comap_of_le
open _root_.AlgebraicGeometry.Scheme hiding IdealSheafData.ideal_comap_of_le
open _root_.AlgebraicGeometry hiding Scheme.IdealSheafData.ideal_comap_of_le

variable {X Y : Scheme.{u}}

theorem ideal_comap_top [IsAffine X] [IsAffine Y] (I : X.IdealSheafData) (f : Y ⟶ X) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top X⟩).map f.appTop.hom :=
  _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_top I f


theorem ideal_comap_of_le (I : X.IdealSheafData) (f : Y ⟶ X) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : (V : Y.Opens) ≤ f ⁻¹ᵁ (U : X.Opens)) :
    (I.comap f).ideal V = (I.ideal U).map (f.appLE U V hVU).hom :=
  _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_le I f U V hVU

theorem ideal_comap_of_isAffineHom (I : X.IdealSheafData) (f : Y ⟶ X) [IsAffineHom f]
    (U : X.affineOpens) :
    (I.comap f).ideal ⟨f ⁻¹ᵁ U, U.2.preimage f⟩ = (I.ideal U).map (f.app U).hom :=
  _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isAffineHom I f U

end AlgebraicGeometry.Scheme.IdealSheafData

namespace ZDFlatG

theorem mem_nonZeroDivisors_of_injective {R S F : Type*} [CommRing R] [CommRing S]
    [FunLike F R S] [MulHomClass F R S] [ZeroHomClass F R S] (e : F) (he : Function.Injective e)
    {r : R} (h : e r ∈ nonZeroDivisors S) : r ∈ nonZeroDivisors R := by
  refine mem_nonZeroDivisors_iff_right.mpr fun z hz => he ?_
  rw [map_zero]
  exact (mem_nonZeroDivisors_iff_right.mp h) _ (by rw [← map_mul, hz, map_zero])

end ZDFlatG

namespace ZDHeadG

theorem finite_preimage_singleton_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) [Finite P] {z : Z}
    (hz : z ∈ Set.range g.base) : (f.base ⁻¹' {z}).Finite := by
  have hr : Set.range fst.base = f.base ⁻¹' Set.range g.base := by
    rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr h.isoPullback.hom.surjective, Set.image_univ,
      Scheme.Pullback.range_fst]
  refine Set.Finite.subset ((Set.finite_range fst.base)) ?_
  rw [hr]
  exact Set.preimage_mono (Set.singleton_subset_iff.mpr hz)

theorem finite_of_isFinite {P : Scheme.{u}} {k : Type u} [Field k] (p : P ⟶ Spec (CommRingCat.of k))
    [IsFinite p] : Finite P := by
  have h := p.finite_preimage_singleton (IsLocalRing.closedPoint k)
  exact Set.finite_univ_iff.mp (h.subset fun y _ => Subsingleton.elim _ _)

section Square

variable {𝒞 S T W : Scheme.{u}} (f : 𝒞 ⟶ S) (g : T ⟶ S) (x : W ⟶ T)
  (F : pullback f (x ≫ g) ⟶ pullback f g)
  (hF1 : F ≫ pullback.fst f g = pullback.fst f (x ≫ g))
  (hF2 : F ≫ pullback.snd f g = pullback.snd f (x ≫ g) ≫ x)

include hF1 hF2

theorem pullbackLeftPullbackSndIso_hom_comp_eq :
    (pullbackLeftPullbackSndIso f g x).hom ≫ F = pullback.fst (pullback.snd f g) x := by
  apply pullback.hom_ext
  · rw [Category.assoc, hF1, pullbackLeftPullbackSndIso_hom_fst]
  · rw [Category.assoc, hF2, pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.condition]

theorem isPullback_mapOnProd :
    IsPullback F (pullback.snd f (x ≫ g)) (pullback.snd f g) x := by
  have e := pullbackLeftPullbackSndIso_hom_comp_eq f g x F hF1 hF2
  refine IsPullback.of_iso (IsPullback.of_hasPullback (pullback.snd f g) x)
    (pullbackLeftPullbackSndIso f g x) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, e]
  · rw [Iso.refl_hom, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

theorem isPullback_snd_comap (Z : (pullback f g).IdealSheafData) :
    IsPullback (pullback.snd F Z.subschemeι) (pullback.fst F Z.subschemeι ≫ pullback.snd f (x ≫ g))
      (Z.subschemeι ≫ pullback.snd f g) x :=
  (IsPullback.of_hasPullback F Z.subschemeι).flip.paste_vert (isPullback_mapOnProd f g x F hF1 hF2)

end Square

theorem isInvertible_comap_of_isIso {X Y : Scheme.{u}} {J : Y.IdealSheafData}
    (hJ : J.IsInvertible) (e : X ⟶ Y) [IsIso e] : (J.comap e).IsInvertible := by
  intro x'
  obtain ⟨U, f, hxf, γ, hγ, hJf⟩ := hJ (e.base x')
  let U' : X.affineOpens := ⟨e ⁻¹ᵁ U.1, U.2.preimage e⟩
  let f' : Γ(X, U') := (e.app U.1).hom f
  have hbo : X.basicOpen f' = e ⁻¹ᵁ Y.basicOpen f := (Scheme.preimage_basicOpen e f).symm
  have hle : (X.affineBasicOpen f' : X.Opens) ≤ e ⁻¹ᵁ (Y.affineBasicOpen f : Y.Opens) := hbo.le
  refine ⟨U', f', ?_, (e.appLE (Y.affineBasicOpen f) (X.affineBasicOpen f') hle).hom γ,
    ?_, ?_⟩
  · rw [hbo]; exact hxf
  · have hiso : IsIso (e.appLE (Y.affineBasicOpen f) (X.affineBasicOpen f') hle) := by
      have heq : (X.affineBasicOpen f' : X.Opens) = e ⁻¹ᵁ (Y.affineBasicOpen f : Y.Opens) := hbo
      rw [Scheme.Hom.appLE, show homOfLE hle = eqToHom heq from Subsingleton.elim _ _, eqToHom_op]
      infer_instance
    let ε := (asIso (e.appLE (Y.affineBasicOpen f) (X.affineBasicOpen f')
      hle)).commRingCatIsoToRingEquiv
    refine ZDFlatG.mem_nonZeroDivisors_of_injective ε.symm ε.symm.injective ?_
    change ε.symm (ε γ) ∈ _
    rw [RingEquiv.symm_apply_apply]
    exact hγ
  · rw [AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_le J e (Y.affineBasicOpen f)
      (X.affineBasicOpen f') hle, hJf, Ideal.map_span, Set.image_singleton]

end ZDHeadG

theorem _root_.AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f] [SmoothOfRelativeDimension 1 f]
    {T : Scheme.{u}} {g : T ⟶ S} [IsLocallyNoetherian T]
    {M : (pullback f g).Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ (pullback f g).Modules ⟶ M) (r : ℕ)
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T),
      ∃ Dx : RelEffCartierDiv f r (x ≫ g),
        Dx.I = (Scheme.Modules.zeroSchemeIdeal s).comap (mapOnProdOver f x rfl)) :
    ∃ D : RelEffCartierDiv f r g,
      D.I = Scheme.Modules.zeroSchemeIdeal s ∧
        ∃ e : M ≅ D.lineBundle, s ≫ e.hom = D.I.invModuleSection := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have geo : ∀ t : T, ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k)
      (x : Spec (CommRingCat.of k) ⟶ T) (pt : Spec (CommRingCat.of k)), x.base pt = t := by
    intro t
    let κ : Type u := T.residueField t
    let k : Type u := AlgebraicClosure κ
    exact ⟨k, inferInstance, inferInstance,
      Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫ T.fromSpecResidueField t,
      IsLocalRing.closedPoint k,
      (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)⟩
  have hfib' : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T),
      ((Scheme.Modules.zeroSchemeIdeal s).comap (pullback.fst (pullback.snd f g)
        x)).IsInvertible := by
    intro k _ _ x
    obtain ⟨Dx, hDx⟩ := hfib k x
    have hinv : ((Scheme.Modules.zeroSchemeIdeal s).comap (mapOnProdOver f x rfl)).IsInvertible :=
      hDx ▸ Dx.isInvertible_I
    rw [← ZDHeadG.pullbackLeftPullbackSndIso_hom_comp_eq f g x (mapOnProdOver f x rfl)
      (mapOnProdOver_fst f x rfl) (mapOnProdOver_snd f x rfl), Scheme.IdealSheafData.comap_comp]
    exact ZDHeadG.isInvertible_comap_of_isIso hinv _
  obtain ⟨hZinv, hZflat⟩ := hM.isInvertible_zeroSchemeIdeal_and_flat (pullback.snd f g) s hfib'
  have := hZflat
  set Z := Scheme.Modules.zeroSchemeIdeal s with hZdef
  have : IsProper (Z.subschemeι ≫ pullback.snd f g) := inferInstance
  have : LocallyQuasiFinite (Z.subschemeι ≫ pullback.snd f g) := by
    rw [locallyQuasiFinite_iff_finite_preimage_singleton]
    intro t
    obtain ⟨k, _, _, x, pt, hpt⟩ := geo t
    obtain ⟨⟨I, hfin, hflat, hlfp, hrk⟩, hDx⟩ := hfib k x
    dsimp only at hDx
    subst hDx
    have h := ZDHeadG.isPullback_snd_comap f g x (mapOnProdOver f x rfl)
      (mapOnProdOver_fst f x rfl) (mapOnProdOver_snd f x rfl) Z
    have : Finite (Z.comap (mapOnProdOver f x rfl)).subscheme := ZDHeadG.finite_of_isFinite
      ((Z.comap (mapOnProdOver f x rfl)).subschemeι ≫ pullback.snd f (x ≫ g))
    have : Finite ↥(pullback (mapOnProdOver f x rfl) Z.subschemeι) :=
      Finite.of_injective _ (Z.comapIso (mapOnProdOver f x rfl)).inv.injective
    exact ZDHeadG.finite_preimage_singleton_of_isPullback h ⟨pt, hpt⟩
  have : IsFinite (Z.subschemeι ≫ pullback.snd f g) := IsFinite.of_isProper_of_locallyQuasiFinite _
  have : LocallyOfFinitePresentation (Z.subschemeι ≫ pullback.snd f g) := inferInstance
  have hrank : ∀ t : T, (Z.subschemeι ≫ pullback.snd f g).finrank t = r := by
    intro t
    obtain ⟨k, _, _, x, pt, hpt⟩ := geo t
    obtain ⟨⟨I, hfin, hflat, hlfp, hrk⟩, hDx⟩ := hfib k x
    dsimp only at hDx
    subst hDx
    have := hfin
    have := hflat
    have h := ZDHeadG.isPullback_snd_comap f g x (mapOnProdOver f x rfl)
      (mapOnProdOver_fst f x rfl) (mapOnProdOver_snd f x rfl) Z
    rw [← hpt, ← Scheme.Hom.finrank_of_isPullback _ _ _ _ h pt]
    have e : pullback.fst (mapOnProdOver f x rfl) Z.subschemeι ≫ pullback.snd f (x ≫ g) =
        (Z.comapIso (mapOnProdOver f x rfl)).inv ≫
          ((Z.comap (mapOnProdOver f x rfl)).subschemeι ≫ pullback.snd f (x ≫ g)) := by
      rw [← Category.assoc, Scheme.IdealSheafData.comapIso_inv_subschemeι]
    rw [e, Scheme.Hom.finrank_comp_left_of_isIso]
    exact hrk pt
  obtain ⟨e, he⟩ := hM.exists_iso_invModule_zeroSchemeIdeal s hZinv
  exact ⟨⟨Z, inferInstance, hZflat, inferInstance, hrank⟩, rfl, e, he⟩
end AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal
end ProofImplementation

open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
  SheafOfModules.isIso_ihomModelToIhom
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
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
attribute [-simp]
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
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.graphOver_fst_assoc
attribute [-simp]
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc

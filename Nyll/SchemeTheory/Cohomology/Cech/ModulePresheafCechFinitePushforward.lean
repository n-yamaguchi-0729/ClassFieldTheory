/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_of_isIntegral_of_ih.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Morphisms.NoetherianFiniteType
public import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafCoherence
public import Nyll.SchemeTheory.Cohomology.Sheaves.ModulePresheafBasicOpenSectionsFree
public import Nyll.SchemeTheory.Cohomology.Cech.ModulePresheafCechFiniteAffSESLeft
public import Nyll.SchemeTheory.Cohomology.Cech.ModulePresheafCechFiniteAffSESMid
public import Nyll.SchemeTheory.Cohomology.Cech.ModulePresheafCechFiniteAffSESRight
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Data.Fintype.EquivFin

/-!
Finiteness of pushforward Cech cohomology by induction on the integral support.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs
namespace OModulePresheaf_cechFinite_pushforward_of_isIntegral_of_ih

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace
open _root_.Opposite

noncomputable section

section
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace
open _root_.Opposite
namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf
namespace PivotAux
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry

theorem support_vanishingIdeal' {V : Scheme.{u}} (Z : Closeds V) :
    (Scheme.IdealSheafData.vanishingIdeal Z).support = Z :=
  SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)

end AlgebraicGeometry.OModulePresheaf.PivotAux
end

section

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace
open _root_.Opposite

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf
namespace PivotAux
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}


end AlgebraicGeometry.OModulePresheaf.PivotAux

end

section

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace
open _root_.Opposite

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf
namespace PivotAux
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}

theorem cechFinite_pow [IsNoetherianRing R] [IsSeparated π] (K : V.OrderedAffineCover)
    {F : OModulePresheaf π} (n : ℕ) (hF : F.CechFinite K) : (F.pow n).CechFinite K := by
  induction n with
  | zero =>
    have hC : ∀ q, Subsingleton ((F.pow 0).cochain K q) :=
      fun q => ⟨fun a b => funext fun s => funext fun k => k.elim0⟩
    exact ⟨(haveI := hC 0; ⟨⟨∅, Subsingleton.elim _ _⟩⟩),
      fun i => (haveI := hC (i + 1); ⟨⟨∅, Subsingleton.elim _ _⟩⟩)⟩
  | succ m ih =>
    exact cechFinite_of_affSES_mid (AffSES.powSucc F m) K ih hF

end AlgebraicGeometry.OModulePresheaf.PivotAux

end

end

open _root_.AlgebraicCurves.Cohomology.Cech.Proofs in
open _root_.AlgebraicGeometry.OModulePresheaf
  OModulePresheaf_cechFinite_pushforward_of_isIntegral_of_ih.AlgebraicGeometry.OModulePresheaf in
theorem _root_.AlgebraicGeometry.OModulePresheaf.cechFinite_pushforward_of_isIntegral_of_ih
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))
      [IsProper π]
    (K : V.OrderedAffineCover) {Z₀ : TopologicalSpace.Closeds V} (hZ₀ : (Z₀ : Set V).Nonempty)
    (hint : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme)
    (hO : (OModulePresheaf.pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal
      Z₀).subschemeι).CechFinite K)
    (ih : ∀ Y' < Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' →
      G.CechFinite K)
    (H : OModulePresheaf ((Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ≫ π))
    (hc : (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι
      H).IsCoherent)
    (hq : (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι
      H).IsQuasicoherent) :
    (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι
      H).CechFinite K := by
  have : IsSeparated π := inferInstance
  have : IsNoetherian V := LocallyOfFiniteType.isNoetherian π
  have : IsLocallyNoetherian V := inferInstance
  let Z₀S := (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme
  let iZ := (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι
  let G : OModulePresheaf π := OModulePresheaf.pushforward π iZ H
  let O : OModulePresheaf π := OModulePresheaf.pushforwardUnit π iZ
  have := hint
  have : IsProper (iZ ≫ π) := inferInstance
  have hOc : O.IsCoherent := isCoherent_pushforwardUnit iZ
  have hOq : O.IsQuasicoherent := isQuasicoherent_pushforwardUnit iZ
  change G.CechFinite K
  obtain ⟨r, Z₁, hZ₁_lt, P, hPc, hPq, α, β, hαbij, hβbij⟩ :
      ∃ (r : ℕ) (Z₁ : Closeds V), Z₁ < Z₀ ∧
        ∃ (P : OModulePresheaf π), P.IsCoherent ∧ P.IsQuasicoherent ∧
        ∃ (α : OModulePresheaf.Hom P G) (β : OModulePresheaf.Hom P (O.pow r)),
          (∀ U : V.affineOpens, ((U : V.Opens) : Set V) ∩ Z₁ = ∅ →
            Function.Bijective (α.app U.1)) ∧
          (∀ U : V.affineOpens, ((U : V.Opens) : Set V) ∩ Z₁ = ∅ →
            Function.Bijective (β.app U.1)) := by
    obtain ⟨U₀, f, hW₀Z, r, y, hψbij⟩ :=
      AlgebraicGeometry.OModulePresheaf.exists_basicOpen_sections_free_of_isIntegral π hZ₀ hint H
        hc hq
    set W₀ := V.basicOpen f
    have hW₀U₀ : W₀ ≤ U₀.1 := V.basicOpen_le f
    set Z₁ : Closeds V := ⟨(Z₀ : Set V) \ W₀, Z₀.2.sdiff W₀.2⟩
    have hZ₁_lt : Z₁ < Z₀ := ⟨fun x hx => hx.1,
      fun h => let ⟨x, hxW, hxZ⟩ := hW₀Z; (h hxZ).2 hxW⟩
    set Or := O.pow r
    let ψ₀ : ∀ (W : V.Opens), W ≤ U₀.1 → Or.obj W →ₗ[R] G.obj W := fun W hWU =>
      letI := (fun O => (Scheme.TwoAffineOpenCover.algebraOfHom (iZ ≫ π) O).toModule) (iZ ⁻¹ᵁ W)
      haveI := H.isScalarTower (iZ ⁻¹ᵁ W)
      ∑ i, ({ toFun := fun mm => (mm i : Γ(Z₀S, iZ ⁻¹ᵁ W)) •
                H.res ((Opens.map iZ.base).monotone hWU) (y i)
              map_add' := fun a b => add_smul _ _ _
              map_smul' := fun c a => smul_assoc c _ _ } :
        (Fin r → Γ(Z₀S, iZ ⁻¹ᵁ W)) →ₗ[R] H.obj (iZ ⁻¹ᵁ W))
    have hψ₀_apply : ∀ {W} (hWU : W ≤ U₀.1) (m : Fin r → Γ(Z₀S, iZ ⁻¹ᵁ W)),
        ψ₀ W hWU m = ∑ i, m i • H.res ((Opens.map iZ.base).monotone hWU) (y i) :=
      fun {W} hWU m => by
        let := (fun O => (Scheme.TwoAffineOpenCover.algebraOfHom (iZ ≫ π) O).toModule) (iZ ⁻¹ᵁ W)
        exact LinearMap.sum_apply (M₂ := H.obj (iZ ⁻¹ᵁ W)) _ _ m
    have hψ₀_Γlin : ∀ {W} (hWU : W ≤ U₀.1) (b : Γ(V, W)) (m : Or.obj W),
        ψ₀ W hWU (b • m) = b • ψ₀ W hWU m := fun {W} hWU b m => by
      let := (fun O => (Scheme.TwoAffineOpenCover.algebraOfHom (iZ ≫ π) O).toModule) (iZ ⁻¹ᵁ W)
      let m' : Fin r → Γ(Z₀S, iZ ⁻¹ᵁ W) := m
      let bm' : Fin r → Γ(Z₀S, iZ ⁻¹ᵁ W) := b • m
      refine (hψ₀_apply hWU bm').trans
        (Eq.trans ?_ (congrArg (b • ·) (hψ₀_apply hWU m').symm))
      change (∑ i, bm' i • H.res ((Opens.map iZ.base).monotone hWU) (y i) : H.obj (iZ ⁻¹ᵁ W))
        = (iZ.appLE W (iZ ⁻¹ᵁ W) le_rfl).hom b
            • ∑ i, m' i • H.res ((Opens.map iZ.base).monotone hWU) (y i)
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_smul _ (m' i) _
    have hψ₀_nat : ∀ {W W' : V.Opens} (hWW' : W ≤ W') (hW'U : W' ≤ U₀.1) (m : Or.obj W'),
        G.res hWW' (ψ₀ W' hW'U m) = ψ₀ W (hWW'.trans hW'U) (Or.res hWW' m) :=
      fun {W W'} hWW' hW'U m => by
        let := (fun O => (Scheme.TwoAffineOpenCover.algebraOfHom (iZ ≫ π) O).toModule) (iZ ⁻¹ᵁ W')
        let := (fun O => (Scheme.TwoAffineOpenCover.algebraOfHom (iZ ≫ π) O).toModule) (iZ ⁻¹ᵁ W)
        let m' : Fin r → Γ(Z₀S, iZ ⁻¹ᵁ W') := m
        let rm' : Fin r → Γ(Z₀S, iZ ⁻¹ᵁ W) := Or.res hWW' m
        refine (congrArg (G.res hWW') (hψ₀_apply hW'U m')).trans
          (Eq.trans ?_ (hψ₀_apply (hWW'.trans hW'U) rm').symm)
        change (H.res ((Opens.map iZ.base).monotone hWW')
              (∑ i, m' i • H.res ((Opens.map iZ.base).monotone hW'U) (y i)) : H.obj (iZ ⁻¹ᵁ W))
          = ∑ i, rm' i • H.res ((Opens.map iZ.base).monotone (hWW'.trans hW'U)) (y i)
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ =>
          (H.res_smul ((Opens.map iZ.base).monotone hWW') (m' i) _).trans
            (congrArg (rm' i • ·) (LinearMap.congr_fun (H.res_comp _ _).symm (y i)))
    let δapp : ∀ U : V.Opens, G.obj U × Or.obj U →ₗ[R] G.obj (U ⊓ W₀) := fun U =>
      (G.res (inf_le_left : U ⊓ W₀ ≤ U)).comp (LinearMap.fst R _ _) -
        (ψ₀ (U ⊓ W₀) (inf_le_right.trans hW₀U₀)).comp
          ((Or.res (inf_le_left : U ⊓ W₀ ≤ U)).comp (LinearMap.snd R _ _))
    have hδapp_apply : ∀ (U : V.Opens) (xm : (G.prod Or).obj U),
        δapp U xm = G.res inf_le_left xm.1
          - ψ₀ (U ⊓ W₀) (inf_le_right.trans hW₀U₀) (Or.res inf_le_left xm.2) := fun U xm => rfl
    let δ : OModulePresheaf.Hom (G.prod Or)
        (G.restrOpen W₀) :=
      { app := δapp
        app_smul := fun U a xm =>
          (congrArg₂ (· - ·) (G.res_smul inf_le_left a xm.1)
            ((congrArg (ψ₀ (U ⊓ W₀) (inf_le_right.trans hW₀U₀))
              (Or.res_smul inf_le_left a xm.2)).trans
              (hψ₀_Γlin (inf_le_right.trans hW₀U₀) _ _))).trans
            (smul_sub ((V.presheaf.map (homOfLE (inf_le_left : U ⊓ W₀ ≤ U)).op).hom a)
              (G.res inf_le_left xm.1)
              (ψ₀ (U ⊓ W₀) (inf_le_right.trans hW₀U₀) (Or.res inf_le_left xm.2))).symm
        naturality := fun {U U'} h => LinearMap.ext fun xm =>
          (congrArg₂ (· - ·)
            ((LinearMap.congr_fun (G.res_comp inf_le_left h).symm xm.1).trans
              (LinearMap.congr_fun (G.res_comp (inf_le_inf_right W₀ h) inf_le_left) xm.1))
            ((congrArg (ψ₀ (U ⊓ W₀) (inf_le_right.trans hW₀U₀))
              ((LinearMap.congr_fun (Or.res_comp inf_le_left h).symm xm.2).trans
                (LinearMap.congr_fun
                  (Or.res_comp (inf_le_inf_right W₀ h) inf_le_left) xm.2))).trans
              (hψ₀_nat (inf_le_inf_right W₀ h) (inf_le_right.trans hW₀U₀)
                (Or.res inf_le_left xm.2)).symm)).trans
            (map_sub (G.res (inf_le_inf_right W₀ h)) _ _).symm }
    let P := OModulePresheaf.ker δ
    let ιP := (OModulePresheaf.kerImSES δ).inc
    let α := (G.fstHom Or).comp ιP
    let β := (G.sndHom Or).comp ιP
    have hαβbij : ∀ U : V.affineOpens, ((U : V.Opens) : Set V) ∩ Z₁ = ∅ →
        Function.Bijective (α.app U.1) ∧ Function.Bijective (β.app U.1) := fun U hU => by
      have hrange : Set.range iZ.base = (Z₀ : Set V) :=
        (Scheme.IdealSheafData.range_subschemeι _).trans
          (congrArg SetLike.coe (PivotAux.support_vanishingIdeal' Z₀))
      have hpre_le : iZ ⁻¹ᵁ U.1 ≤ iZ ⁻¹ᵁ (U.1 ⊓ W₀) := fun z hz =>
        ⟨hz, not_not.mp fun hnw => Set.eq_empty_iff_forall_notMem.mp hU (iZ.base z)
          ⟨hz, hrange ▸ Set.mem_range_self z, hnw⟩⟩
      have hGres_bij : Function.Bijective (G.res (inf_le_left : U.1 ⊓ W₀ ≤ U.1)) := by
        change Function.Bijective (H.res _)
        exact ⟨Function.LeftInverse.injective (g := H.res hpre_le) fun a =>
            LinearMap.congr_fun ((H.res_comp hpre_le _).symm.trans (H.res_refl _)) a,
          Function.RightInverse.surjective (g := H.res hpre_le) fun a =>
            LinearMap.congr_fun ((H.res_comp _ hpre_le).symm.trans (H.res_refl _)) a⟩
      have hOrres_bij : Function.Bijective (Or.res (inf_le_left : U.1 ⊓ W₀ ≤ U.1)) := by
        let S := OModulePresheaf.unit (iZ ≫ π)
        have hSbij : Function.Bijective (S.res
            ((Opens.map iZ.base).monotone (inf_le_left : U.1 ⊓ W₀ ≤ U.1))) :=
          ⟨Function.LeftInverse.injective (g := S.res hpre_le) fun a =>
              LinearMap.congr_fun ((S.res_comp hpre_le _).symm.trans (S.res_refl _)) a,
            Function.RightInverse.surjective (g := S.res hpre_le) fun a =>
              LinearMap.congr_fun ((S.res_comp _ hpre_le).symm.trans (S.res_refl _)) a⟩
        exact ⟨fun a b hab => funext fun i => hSbij.1 (congrFun hab i),
          fun c => ⟨fun i => (hSbij.2 (c i)).choose, funext fun i => (hSbij.2 (c i)).choose_spec⟩⟩
      have hψ₀_bij : Function.Bijective (ψ₀ (U.1 ⊓ W₀) (inf_le_right.trans hW₀U₀)) :=
        (funext (hψ₀_apply (W := U.1 ⊓ W₀) (inf_le_right.trans hW₀U₀)) :
            ⇑(ψ₀ (U.1 ⊓ W₀) (inf_le_right.trans hW₀U₀)) = _).symm ▸
          hψbij (U.1 ⊓ W₀) inf_le_right (Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated
            π U.2 (U₀.2.basicOpen f))
      have hψOr_bij := hψ₀_bij.comp hOrres_bij
      have hδeq : ∀ (p : P.obj U.1), G.res inf_le_left p.1.1
          = ψ₀ (U.1 ⊓ W₀) (inf_le_right.trans hW₀U₀) (Or.res inf_le_left p.1.2) := fun p =>
        sub_eq_zero.mp (LinearMap.mem_ker.mp p.2)
      refine ⟨⟨fun p₁ p₂ hp => Subtype.ext (Prod.ext hp (hψOr_bij.1
          ((hδeq p₁).symm.trans ((congrArg (G.res inf_le_left) (show p₁.1.1 = p₂.1.1 from hp)).trans
            (hδeq p₂))))), fun x =>
          let ⟨m, hm⟩ := hψOr_bij.2 (G.res inf_le_left x)
          ⟨⟨(x, m), LinearMap.mem_ker.mpr (sub_eq_zero.mpr hm.symm)⟩, rfl⟩⟩,
        ⟨fun p₁ p₂ hp => Subtype.ext (Prod.ext (hGres_bij.1
          ((hδeq p₁).trans ((congrArg _ (congrArg (Or.res inf_le_left)
            (show p₁.1.2 = p₂.1.2 from hp))).trans (hδeq p₂).symm))) hp), fun m =>
          let ⟨x, hx⟩ := hGres_bij.2 (ψ₀ _ (inf_le_right.trans hW₀U₀) (Or.res inf_le_left m))
          ⟨⟨(x, m), LinearMap.mem_ker.mpr (sub_eq_zero.mpr hx)⟩, rfl⟩⟩⟩
    have haff : ∀ U : V.affineOpens, IsAffineOpen (U.1 ⊓ W₀) := fun U =>
      Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated π U.2 (U₀.2.basicOpen f)
    exact ⟨r, Z₁, hZ₁_lt, P,
      isCoherent_ker δ (isCoherent_prod hc
        (isCoherent_pow r hOc)),
      isQuasicoherent_ker δ (isQuasicoherent_prod hq
        (isQuasicoherent_pow r hOq)) (isQuasicoherent_restrOpen W₀ haff hq),
      α, β, fun U hU => (hαβbij U hU).1, fun U hU => (hαβbij U hU).2⟩
  have hOr : (O.pow r).CechFinite K :=
    PivotAux.cechFinite_pow K r hO
  have hOrc : (O.pow r).IsCoherent :=
    isCoherent_pow r hOc
  have hOrq : (O.pow r).IsQuasicoherent :=
    isQuasicoherent_pow r hOq
  have hflk : ∀ {F' G' : OModulePresheaf π} (φ : OModulePresheaf.Hom F' G')
      (_ : F'.IsCoherent) (_ : F'.IsQuasicoherent)
      (_ : G'.IsCoherent) (_ : G'.IsQuasicoherent)
      (_ : ∀ U : V.affineOpens, ((U : V.Opens) : Set V) ∩ Z₁ = ∅ →
        Function.Bijective (φ.app U.1)),
      (OModulePresheaf.ker φ).CechFinite K ∧
        (OModulePresheaf.coker φ).CechFinite K := by
    intro F' G' φ hF'c hF'q hG'c hG'q hbij
    exact ⟨ih Z₁ hZ₁_lt _ (isCoherent_ker φ hF'c)
        (isQuasicoherent_ker φ hF'q hG'q)
        (fun U hU => ⟨fun a b => Subtype.ext ((hbij U hU).1 (a.2.trans b.2.symm))⟩),
      ih Z₁ hZ₁_lt _ (isCoherent_coker φ hG'c)
        (isQuasicoherent_coker φ hG'q hF'q)
        (fun U hU => Submodule.Quotient.subsingleton_iff.mpr
          (LinearMap.range_eq_top.mpr (hbij U hU).2))⟩
  obtain ⟨hkβ, hcβ⟩ := hflk β hPc hPq hOrc hOrq hβbij
  have himβ : (OModulePresheaf.im β).CechFinite K :=
    OModulePresheaf.cechFinite_of_affSES_left (OModulePresheaf.imCokerSES β).toAffSES K hOr hcβ
  have hP : P.CechFinite K :=
    OModulePresheaf.cechFinite_of_affSES_mid (OModulePresheaf.kerImSES β).toAffSES K hkβ himβ
  obtain ⟨hkα, hcα⟩ := hflk α hPc hPq hc hq hαbij
  have himα : (OModulePresheaf.im α).CechFinite K :=
    OModulePresheaf.cechFinite_of_affSES_right (OModulePresheaf.kerImSES α).toAffSES K hkα hP
  exact OModulePresheaf.cechFinite_of_affSES_mid (OModulePresheaf.imCokerSES α).toAffSES K himα hcα
end OModulePresheaf_cechFinite_pushforward_of_isIntegral_of_ih
end AlgebraicCurves.Cohomology.Cech.Proofs
end ProofImplementation

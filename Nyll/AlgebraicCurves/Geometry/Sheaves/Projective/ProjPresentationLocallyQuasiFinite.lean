/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_locallyQuasiFinite_of_forall_exists_eq_sum_smul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteBySectionsFinite
public import Nyll.SchemeTheory.ProjectiveSpace.AwayRatio

/-!
# Local quasi-finiteness of projective presentations
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_ProjPresentation_locallyQuasiFinite_of_forall_exists_eq_sum_smul

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.TopologicalSpace
open _root_.MvPolynomial
open _root_.HomogeneousLocalization
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace SF
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_FiniteBySections_isFinite_of_unit
open AlgebraicGeometry.Scheme.Modules.FBSUnit

section Main

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N N' :
    ℕ}
  (𝔓 : M.ProjPresentation f N) (𝔔 : M.ProjPresentation f N')

theorem quasiFinite_chartRing (i : Fin (N + 1)) (j : Fin (N' + 1)) (V : X.Opens) (hV : IsAffineOpen
    V)
    (hVi : V ≤ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
        (MvPolynomial.X i))
    (hVj : V ≤ 𝔔.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)
        (MvPolynomial.X j))
    (c : Fin (N + 1) → Fin (N' + 1) → R)
    (hc : ∀ l, resTop M (𝔓.σ l) V = ∑ k, algR f V (c l k) • resTop M (𝔔.σ k) V)
    (hα : (chartRing 𝔓.toProj i V hVi).QuasiFinite) :
    (chartRing 𝔔.toProj j V hVj).QuasiFinite := by
  classical
  set α := chartRing 𝔓.toProj i V hVi with hαdef
  set β := chartRing 𝔔.toProj j V hVj with hβdef
  have hFi : IsFrameOn M (𝔓.σ i) V := isFrameOn 𝔓 i V hVi
  have hFj : IsFrameOn M (𝔔.σ j) V := isFrameOn 𝔔 j V hVj
  let Ay := Away (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R) (MvPolynomial.X j :
      MvPolynomial (Fin (N' + 1)) R)
  let a : Fin (N + 1) → Ay := fun l => ∑ k, algebraMap R Ay (c l k) * ProjSpace.ratio R N' j k
  have hβa : ∀ l, β (a l) • resTop M (𝔔.σ j) V = resTop M (𝔓.σ l) V := by
    intro l
    simp only [a, map_sum, map_mul, Finset.sum_smul, mul_smul]
    rw [hc l]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hβdef, chartRing_algebraMap f 𝔔.toProj j V hVj hV 𝔔.toProj_π, chartRing_ratio_smul 𝔔 j V
        hVj k]
  have hu : IsUnit (β (a i)) := hFj.isUnit_of_eq_smul hFi _ (hβa i).symm
  have hαr : ∀ l, α (ProjSpace.ratio R N i l) * β (a i) = β (a l) := by
    intro l
    apply hFj.injective
    show (α (ProjSpace.ratio R N i l) * β (a i)) • resTop M (𝔔.σ j) V = β (a l) • resTop M (𝔔.σ j) V
    rw [mul_smul, hβa i, hαdef, chartRing_ratio_smul 𝔓 i V hVi l, hβa l]
  let βt : Localization.Away (a i) →+* Γ(X, V) :=
    IsLocalization.Away.lift (S := Localization.Away (a i)) (a i) (g := β) hu
  have hβt : βt.comp (algebraMap Ay (Localization.Away (a i))) = β :=
    IsLocalization.Away.lift_comp (S := Localization.Away (a i)) (a i) hu
  have hβt' : ∀ y, βt (algebraMap Ay (Localization.Away (a i)) y) = β y := fun y =>
    IsLocalization.Away.lift_eq (S := Localization.Away (a i)) (a i) hu y
  have algRB_apply : ∀ r, algebraMap R (Localization.Away (a i)) r
      = algebraMap Ay (Localization.Away (a i)) (algebraMap R Ay r) := fun r =>
    IsScalarTower.algebraMap_apply R Ay (Localization.Away (a i)) r
  obtain ⟨γ, hγ⟩ := ProjSpace.exists_algHom_away_apply_ratio_eq R N i (B := Localization.Away (a i))
    (fun l => algebraMap Ay (Localization.Away (a i)) (a l) * IsLocalization.Away.invSelf (a i))
    (by exact IsLocalization.Away.mul_invSelf (a i))
  let algRV : Algebra R Γ(X, V) := (β.comp (algebraMap R Ay)).toAlgebra
  have algRV_apply : ∀ r, algebraMap R Γ(X, V) r = β (algebraMap R Ay r) := fun r => rfl
  have hαβR : ∀ r, α (algebraMap R _ r) = β (algebraMap R Ay r) := fun r =>
    (chartRing_algebraMap f 𝔓.toProj i V hVi hV 𝔓.toProj_π r).trans
      (chartRing_algebraMap f 𝔔.toProj j V hVj hV 𝔔.toProj_π r).symm
  let αA : Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i :
      MvPolynomial (Fin (N + 1)) R)
      →ₐ[R] Γ(X, V) :=
    { α with
      commutes' := fun r => by
        rw [algRV_apply]
        exact hαβR r }
  let βtA : Localization.Away (a i) →ₐ[R] Γ(X, V) :=
    { βt with
      commutes' := fun r => by
        rw [algRB_apply, algRV_apply]
        exact hβt' _ }
  have hinv : βt (IsLocalization.Away.invSelf (a i)) * β (a i) = 1 := by
    rw [← hβt' (a i), ← map_mul, mul_comm]
    exact (congrArg βt (IsLocalization.Away.mul_invSelf (S := Localization.Away (a i)) (a
        i))).trans (map_one βt)
  have hAlg : αA = βtA.comp γ := by
    apply AlgHom.ext_of_adjoin_eq_top (ProjSpace.adjoin_range_ratio R N i)
    rintro _ ⟨l, rfl⟩
    change α (ProjSpace.ratio R N i l) = βt (γ (ProjSpace.ratio R N i l))
    rw [hγ, map_mul, hβt']
    calc α (ProjSpace.ratio R N i l)
        = α (ProjSpace.ratio R N i l) * (βt (IsLocalization.Away.invSelf (a i)) * β (a i)) := by
          rw [hinv, mul_one]
      _ = (α (ProjSpace.ratio R N i l) * β (a i)) * βt (IsLocalization.Away.invSelf (a i)) := by
          ring
      _ = β (a l) * βt (IsLocalization.Away.invSelf (a i)) := by rw [hαr]
  have key : α = βt.comp γ.toRingHom := by
    have := congrArg AlgHom.toRingHom hAlg
    exact this
  have h1 : (βt.comp γ.toRingHom).QuasiFinite := key ▸ hα
  have h2 := RingHom.QuasiFinite.of_comp (f := βt) (g := γ.toRingHom) h1
  have h3 := RingHom.QuasiFinite.holdsForLocalizationAway (Localization.Away (a i)) (a i)
  rw [← hβt]
  exact RingHom.QuasiFinite.comp h2 h3

theorem quasiFinite_appLE_iff (t : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (i
    : Fin (N + 1))
    (V : X.Opens)
    (hle : V ≤ t ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
        (MvPolynomial.X i)) :
    (t.appLE (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X
        i)) V hle).hom.QuasiFinite
      ↔ (chartRing t i V hle).QuasiFinite := by
  let e := (Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X i)
    (ProjSpace.X_mem_one R N i) one_pos).commRingCatIsoToRingEquiv
  have he : (chartRing t i V hle) =
      (t.appLE (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X
          i)) V hle).hom.comp
        e.toRingHom := by
    ext z
    change _ = (t.appLE _ V hle) ((Proj.basicOpenIsoAway _ (MvPolynomial.X i) (ProjSpace.X_mem_one
        R N i) one_pos).hom z)
    rw [Proj.basicOpenIsoAway_hom]
    rfl
  constructor
  · intro h
    rw [he]
    exact RingHom.QuasiFinite.respectsIso.2 _ e h
  · intro h
    have h' := RingHom.QuasiFinite.respectsIso.2 _ e.symm h
    rw [he] at h'
    convert h' using 1
    ext z
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]

theorem hc_res (c : Fin (N + 1) → Fin (N' + 1) → R)
    (hc : ∀ l, 𝔓.σ l = ∑ k, (f.appTop ((Scheme.ΓSpecIso (.of R)).inv (c l k))) • 𝔔.σ k) (V :
        X.Opens) (l : Fin (N + 1)) :
    resTop M (𝔓.σ l) V = ∑ k, algR f V (c l k) • resTop M (𝔔.σ k) V := by
  have h := congrArg (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) (hc l)
  rw [map_sum] at h
  refine h.trans (Finset.sum_congr rfl fun k _ => ?_)
  rw [Modules.map_smul]
  rfl

theorem locallyQuasiFinite [LocallyQuasiFinite 𝔓.toProj]
    (h : ∀ i : Fin (N + 1), ∃ c : Fin (N' + 1) → R,
      𝔓.σ i = ∑ j, (f.appTop ((Scheme.ΓSpecIso (.of R)).inv (c j))) • 𝔔.σ j) :
    LocallyQuasiFinite 𝔔.toProj := by
  classical
  choose c hc using h
  have hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource @RingHom.QuasiFinite :=
    (RingHom.QuasiFinite.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.QuasiFinite.holdsForLocalizationAway).1
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyQuasiFinite) hQ]
  intro x
  have hcovP : (⨆ i : Fin (N + 1), Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1))
      R)
      (MvPolynomial.X i)) = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X R N)
  have hcovQ : (⨆ j : Fin (N' + 1), Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' +
      1)) R)
      (MvPolynomial.X j)) = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X R N')
  have hxP : 𝔓.toProj.base x ∈ (⨆ i : Fin (N + 1), Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X i)) := by rw [hcovP]; trivial
  have hxQ : 𝔔.toProj.base x ∈ (⨆ j : Fin (N' + 1), Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)
      (MvPolynomial.X j)) := by rw [hcovQ]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxP
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxQ
  let W : X.Opens := (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1))
      R)
      (MvPolynomial.X i)) ⊓
    (𝔔.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)
        (MvPolynomial.X j))
  have hxW : x ∈ W := ⟨hi, hj⟩
  obtain ⟨_, ⟨V, hVaff, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.2
  have hVi : V ≤ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X i) := fun p hp => (hVW hp).1
  have hVj : V ≤ 𝔔.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R)
      (MvPolynomial.X j) := fun p hp => (hVW hp).2
  refine ⟨⟨_, Proj.isAffineOpen_basicOpen _ (MvPolynomial.X j) (ProjSpace.X_mem_one R N' j)
      one_pos⟩, ⟨V, hVaff⟩,
    hxV, hVj, ?_⟩
  have hα : (chartRing 𝔓.toProj i V hVi).QuasiFinite := by
    rw [← quasiFinite_appLE_iff]
    exact HasRingHomProperty.appLE @LocallyQuasiFinite 𝔓.toProj inferInstance
      ⟨_, Proj.isAffineOpen_basicOpen _ (MvPolynomial.X i) (ProjSpace.X_mem_one R N i) one_pos⟩ ⟨V,
          hVaff⟩ hVi
  change (𝔔.toProj.appLE _ V hVj).hom.QuasiFinite
  rw [quasiFinite_appLE_iff]
  exact quasiFinite_chartRing 𝔓 𝔔 i j V hVaff hVi hVj c (hc_res 𝔓 𝔔 c hc V) hα

end Main

end

end AlgebraicGeometry.Scheme.Modules.SF

end Scheme_Modules_ProjPresentation_locallyQuasiFinite_of_forall_exists_eq_sum_smul
end AlgebraicCurves.Geometry.Sheaves.Proofs

namespace AlgebraicGeometry.Scheme.Modules.ProjPresentation

universe u

open _root_.AlgebraicCurves.Geometry.Sheaves.Proofs in
open CategoryTheory _root_.AlgebraicGeometry
  Scheme_Modules_ProjPresentation_locallyQuasiFinite_of_forall_exists_eq_sum_smul.AlgebraicGeometry
in
attribute [local instance] MvPolynomial.gradedAlgebra in
theorem locallyQuasiFinite_of_forall_exists_eq_sum_smul
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M : X.Modules} {N N' : ℕ}
    (𝔓 : M.ProjPresentation f N) (𝔔 : M.ProjPresentation f N') [LocallyQuasiFinite 𝔓.toProj]
    (h : ∀ i : Fin (N + 1), ∃ c : Fin (N' + 1) → R,
      𝔓.σ i = ∑ j, (f.appTop ((Scheme.ΓSpecIso (.of R)).inv (c j))) • 𝔔.σ j) :
    LocallyQuasiFinite 𝔔.toProj :=
  Scheme.Modules.SF.locallyQuasiFinite 𝔓 𝔔 h
end AlgebraicGeometry.Scheme.Modules.ProjPresentation
end ProofImplementation

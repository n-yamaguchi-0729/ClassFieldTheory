/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_rankAtStalk_sections_eq_one_of_locallyTrivial.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Modules.Frames.FrameBridge
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Nyll.SchemeTheory.Modules.Localization.LocallyTrivialSectionsLocalization
public import Nyll.SchemeTheory.Modules.Sections.FiniteSectionsLocallyTrivial
/-!
# Rank one of sections of a locally trivial module

The affine section module of a locally trivial module sheaf has rank one at each stalk,
using the localized module on a trivializing basic open.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.LocalTrivialization (rM rO rM_rM rO_rO rM_self rO_self
  rM_smul hat_eq le_hat hat_le eApp eInv eInv_eApp eApp_eInv eApp_zero eApp_injective
  restrict_smul_eq eApp_smul unit_map_eq eApp_res ψ ψinv rM_roundtrip rM_roundtrip' rO_roundtrip
  rO_roundtrip' ψ_ψinv ψinv_ψ ψ_injective ψ_zero ψ_smul ψ_res)

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_rankAtStalk_sections_eq_one_of_locallyTrivial

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace
open _root_.Opposite

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace SectRank
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

section Loc


variable {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens) (f : Γ(X, U.1))
  (V : X.Opens) (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)
  (hfV : X.basicOpen f ≤ V)

theorem ψ_add {W : X.Opens} (hWV : W ≤ V) (m m' : Γ(M, W)) :
    ψ M V e hWV (m + m') = ψ M V e hWV m + ψ M V e hWV m' := by
  simp only [ψ, rM, rO, eApp, map_add]
  erw [AddMonoidHom.map_add, RingHom.map_add]

/-- The linear map from affine module sections to coordinate sections on a trivializing basic open.
-/
noncomputable def gψ : Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(X, X.basicOpen f) where
  toFun m := ψ M V e hfV (rM M (X.basicOpen_le f) m)
  map_add' m m' := by
    simp only [rM, map_add]
    exact ψ_add M V e hfV _ _
  map_smul' a m := by
    simp only [RingHom.id_apply]
    rw [rM_smul, ψ_smul, Algebra.smul_def]
    rfl

theorem gψ_apply (m : Γ(M, U.1)) : gψ M U f V e hfV m = ψ M V e hfV (rM M (X.basicOpen_le f) m) :=
  rfl

include hfV in
theorem isLocalizedModule_gψ
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
          :
    IsLocalizedModule (Submonoid.powers f) (gψ M U f V e hfV) where
  map_units s := by
    have := U.2.isLocalization_basicOpen f
    exact IsLocalizedModule.map_units (Algebra.linearMap Γ(X, U.1) Γ(X, X.basicOpen f)) s
  surj b := by
    obtain ⟨n, y, hy⟩ := (isLocalization_basicOpen_of_locallyTrivial M htriv U f).1 (ψinv M V e hfV
        b)
    refine ⟨(y, ⟨f ^ n, n, rfl⟩), ?_⟩
    change (f ^ n : Γ(X, U.1)) • b = ψ M V e hfV (rM M (X.basicOpen_le f) y)
    change (f ^ n : Γ(X, U.1)) • b = ψ M V e hfV (M.presheaf.map (homOfLE (X.basicOpen_le f)).op y)
    rw [hy, ψ_smul, ψ_ψinv, Algebra.smul_def]
    rfl
  exists_of_eq {m m'} h := by
    have h' : rM M (X.basicOpen_le f) m = rM M (X.basicOpen_le f) m' := ψ_injective M V e hfV h
    have h0 : M.presheaf.map (homOfLE (X.basicOpen_le f)).op (m - m') = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr h'
    obtain ⟨n, hn⟩ := (isLocalization_basicOpen_of_locallyTrivial M htriv U f).2 _ h0
    refine ⟨⟨f ^ n, n, rfl⟩, ?_⟩
    rw [smul_sub, sub_eq_zero] at hn
    exact hn

end Loc

theorem rankAtStalk_sections
    {X : Scheme.{u}} (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.affineOpens) (𝔭 : PrimeSpectrum Γ(X, U.1)) :
    Module.rankAtStalk (R := Γ(X, U.1)) Γ(M, U.1) 𝔭 = 1 := by
  classical
  have hfin : Module.Finite Γ(X, U.1) Γ(M, U.1) := finite_sections_of_locallyTrivial M htriv U
  let s : Set Γ(X, U.1) := {f | ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit
      V.toScheme.ringCatSheaf),
    X.basicOpen f ≤ V}
  have hspan : Ideal.span s = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    intro p hp
    obtain ⟨V, hxV, ⟨e⟩⟩ := htriv p
    obtain ⟨h, hhV, hph⟩ := U.2.exists_basicOpen_le ⟨p, hxV⟩ hp
    exact Opens.mem_iSup.mpr ⟨⟨h, V, (restrictFunctorIsoPullback V.ι).app M ≪≫ e, hhV⟩, hph⟩
  have hdata : ∀ r : s, ∃ (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit
      V.toScheme.ringCatSheaf),
      X.basicOpen r.1 ≤ V := fun r => r.2
  choose V e hle using hdata
  have hloc : ∀ r : s, IsLocalizedModule (Submonoid.powers r.1) (gψ M U r.1 (V r) (e r) (hle r)) :=
    fun r => isLocalizedModule_gψ M U r.1 (V r) (e r) (hle r) htriv
  have hflat : Module.Flat Γ(X, U.1) Γ(M, U.1) :=
    Module.flat_of_isLocalized_span (R := Γ(X, U.1)) Γ(X, U.1) Γ(M, U.1) s hspan
      (fun r => Γ(X, X.basicOpen r.1)) (fun r => gψ M U r.1 (V r) (e r) (hle r)) fun r => by
        have := U.2.isLocalization_basicOpen r.1
        exact IsLocalization.flat Γ(X, X.basicOpen r.1) (Submonoid.powers r.1)
  have hns : ¬ (s ⊆ 𝔭.asIdeal) := fun hsub =>
    𝔭.isPrime.ne_top (top_le_iff.mp (hspan ▸ Ideal.span_le.mpr hsub))
  obtain ⟨f, hfs, hfp⟩ := Set.not_subset.mp hns
  have := U.2.isLocalization_basicOpen f
  have := hloc ⟨f, hfs⟩
  have hmem : 𝔭 ∈ Set.range (PrimeSpectrum.comap (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f))) := by
    rw [PrimeSpectrum.localization_away_comap_range Γ(X, X.basicOpen f) f]
    exact hfp
  obtain ⟨q, rfl⟩ := hmem
  have : Nontrivial Γ(X, X.basicOpen f) := PrimeSpectrum.nontrivial q
  rw [← Module.rankAtStalk_baseChange,
    Module.rankAtStalk_eq_of_equiv
      (IsLocalizedModule.isBaseChange (Submonoid.powers f) Γ(X, X.basicOpen f)
        (gψ M U f (V ⟨f, hfs⟩) (e ⟨f, hfs⟩) (hle ⟨f, hfs⟩))).equiv,
    Module.rankAtStalk_self]
  rfl

end AlgebraicGeometry.Scheme.Modules.SectRank

theorem _root_.AlgebraicGeometry.Scheme.Modules.rankAtStalk_sections_eq_one_of_locallyTrivial
    {X : Scheme.{u}} (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.affineOpens) (𝔭 : PrimeSpectrum Γ(X, U.1)) :
    Module.rankAtStalk (R := Γ(X, U.1)) Γ(M, U.1) 𝔭 = 1 :=
  AlgebraicGeometry.Scheme.Modules.SectRank.rankAtStalk_sections M htriv U 𝔭
end Scheme_Modules_rankAtStalk_sections_eq_one_of_locallyTrivial
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

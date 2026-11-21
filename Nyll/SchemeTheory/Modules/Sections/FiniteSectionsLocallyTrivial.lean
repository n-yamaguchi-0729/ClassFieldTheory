/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_finite_sections_of_locallyTrivial.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Modules.Frames.FrameBridge
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Nyll.SchemeTheory.Modules.Localization.LocallyTrivialSectionsLocalization
/-!
# Finite section modules of locally trivial sheaves

Local trivializations on basic opens and a finite affine cover provide finite generation
of module sections over an affine open.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.LocalTrivialization (rM rO rM_rM rO_rO rM_self rO_self
  rM_smul hat_eq le_hat hat_le eApp eInv eInv_eApp eApp_eInv eApp_zero eApp_injective
  restrict_smul_eq eApp_smul unit_map_eq eApp_res ψ ψinv rM_roundtrip rM_roundtrip' rO_roundtrip
  rO_roundtrip' ψ_ψinv ψinv_ψ ψ_injective ψ_zero ψ_smul ψ_res)

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_finite_sections_of_locallyTrivial

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
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

theorem finite_sections_of_locallyTrivial'
    {X : Scheme.{u}} (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.affineOpens) :
    Module.Finite Γ(X, U.1) Γ(M, U.1) := by
  classical
  have hbasis : ∀ x : U.1, ∃ (h : Γ(X, U.1)) (V : X.Opens) (_ : M.restrict V.ι ≅ SheafOfModules.unit
      V.toScheme.ringCatSheaf),
      (x : X) ∈ X.basicOpen h ∧ X.basicOpen h ≤ V := by
    intro x
    obtain ⟨V, hxV, ⟨e⟩⟩ := htriv x
    obtain ⟨h, hhV, hxh⟩ := U.2.exists_basicOpen_le ⟨(x : X), hxV⟩ x.2
    exact ⟨h, V, (restrictFunctorIsoPullback V.ι).app M ≪≫ e, hxh, hhV⟩
  choose hOf VOf eOf hxh hhV using hbasis
  have hcov : (U.1 : Set X) ⊆ ⋃ x : U.1, (X.basicOpen (hOf x) : Set X) := fun p hp =>
    Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hxh ⟨p, hp⟩⟩
  obtain ⟨t, ht⟩ := U.2.isCompact.elim_finite_subcover (fun x : U.1 => (X.basicOpen (hOf x) : Set
      X))
    (fun x => (X.basicOpen (hOf x)).isOpen) hcov
  have hspan : Ideal.span ((fun x : U.1 => hOf x) '' (↑t : Set _)) = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    intro p hp
    have := ht hp
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hxt, hpx⟩ := this
    exact Opens.mem_iSup.mpr ⟨⟨hOf x, Set.mem_image_of_mem _ (Finset.mem_coe.mpr hxt)⟩, hpx⟩
  have hDV : ∀ x, X.basicOpen (hOf x) ≤ VOf x := fun x => hhV x
  let u : ∀ x : U.1, Γ(M, X.basicOpen (hOf x)) := fun x => ψinv M (VOf x) (eOf x) (hDV x) 1
  have hu : ∀ x (z : Γ(M, X.basicOpen (hOf x))), z = ψ M (VOf x) (eOf x) (hDV x) z • u x := by
    intro x z
    apply ψ_injective M (VOf x) (eOf x) (hDV x)
    rw [ψ_smul, ψ_ψinv, mul_one]
  have hloc := fun x => isLocalization_basicOpen_of_locallyTrivial M htriv U (hOf x)
  have step : ∀ x : U.1, ∃ (n : ℕ) (y : Γ(M, U.1)),
      rM M (X.basicOpen_le (hOf x)) y = rO (X.basicOpen_le (hOf x)) (hOf x ^ n) • u x :=
    fun x => (hloc x).1 (u x)
  choose n y hy using step
  have key : ∀ (m : Γ(M, U.1)) (x : U.1), ∃ e : ℕ,
      (hOf x ^ e : Γ(X, U.1)) • m ∈ Submodule.span Γ(X, U.1) ({y x} : Set Γ(M, U.1)) := by
    intro m x
    have := U.2.isLocalization_basicOpen (hOf x)
    have hle : X.basicOpen (hOf x) ≤ U.1 := X.basicOpen_le (hOf x)
    obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hab⟩ := IsLocalization.surj (Submonoid.powers (hOf x))
      (ψ M (VOf x) (eOf x) (hDV x) (rM M hle m))
    have hab' : ψ M (VOf x) (eOf x) (hDV x) (rM M hle m) * rO hle (hOf x ^ k) = rO hle b := hab
    have hzero : rM M hle ((hOf x ^ (k + n x) : Γ(X, U.1)) • m - b • y x) = 0 := by
      change (M.presheaf.map (homOfLE hle).op) (_ - _) = 0
      rw [map_sub]
      change rM M hle ((hOf x ^ (k + n x) : Γ(X, U.1)) • m) - rM M hle (b • y x) = 0
      rw [rM_smul, rM_smul, hy, hu x (rM M hle m), ← mul_smul, ← mul_smul, ← sub_smul]
      have hcoef : rO hle (hOf x ^ (k + n x)) * ψ M (VOf x) (eOf x) (hDV x) (rM M hle m)
          = rO hle b * rO hle (hOf x ^ n x) := by
        rw [← hab']
        simp only [rO, map_pow, map_mul, pow_add]
        ring
      rw [hcoef, sub_self, zero_smul]
    obtain ⟨N, hN⟩ := (hloc x).2 _ hzero
    rw [smul_sub, sub_eq_zero] at hN
    refine ⟨N + (k + n x), ?_⟩
    rw [pow_add, mul_smul, hN, ← mul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  refine Module.finite_def.mpr ⟨t.image y, ?_⟩
  rw [eq_top_iff]
  intro m _
  choose e he using key m
  obtain ⟨emax, hemax⟩ : ∃ N : ℕ, ∀ x ∈ t, e x ≤ N := ⟨t.sup e, fun x hx => Finset.le_sup (f := e)
      hx⟩
  have hmono : ∀ x ∈ t, (hOf x ^ emax : Γ(X, U.1)) • m ∈ Submodule.span Γ(X, U.1) (↑(t.image y) :
      Set Γ(M, U.1)) := by
    intro x hx
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (hemax x hx)
    rw [hd, add_comm, pow_add, mul_smul]
    refine Submodule.smul_mem _ _ (Submodule.span_mono ?_ (he x))
    rw [Finset.coe_image, Set.singleton_subset_iff]
    exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr hx)
  have hspan' : Ideal.span ((fun x : U.1 => hOf x ^ emax) '' (↑t : Set _)) = ⊤ := by
    have := Ideal.span_pow_eq_top (α := Γ(X, U.1)) ((fun x : U.1 => hOf x) '' (↑t : Set _)) hspan
        emax
    rwa [Set.image_image] at this
  have h1 : (1 : Γ(X, U.1)) ∈ Ideal.span ((fun x : U.1 => hOf x ^ emax) '' (↑t : Set _)) := by
    rw [hspan']; trivial
  rw [← one_smul Γ(X, U.1) m]
  refine Submodule.span_induction (p := fun r _ => r • m ∈ Submodule.span Γ(X, U.1) (↑(t.image y) :
      Set Γ(M, U.1)))
    ?_ ?_ ?_ ?_ h1
  · rintro _ ⟨x, hx, rfl⟩
    change (hOf x ^ emax) • m ∈ _
    exact hmono x (Finset.mem_coe.mp hx)
  · change (0 : Γ(X, U.1)) • m ∈ _
    rw [zero_smul]; exact Submodule.zero_mem _
  · intro r s _ _ hr hs
    change (r + s) • m ∈ _
    rw [add_smul]; exact Submodule.add_mem _ hr hs
  · intro c r _ hr
    change (c • r) • m ∈ _
    rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ _ hr

end AlgebraicGeometry.Scheme.Modules

theorem _root_.AlgebraicGeometry.Scheme.Modules.finite_sections_of_locallyTrivial
    {X : Scheme.{u}} (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.affineOpens) :
    Module.Finite Γ(X, U.1) Γ(M, U.1) :=
  AlgebraicGeometry.Scheme.Modules.finite_sections_of_locallyTrivial' M htriv U
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_finite_sections_of_locallyTrivial
end ProofImplementation

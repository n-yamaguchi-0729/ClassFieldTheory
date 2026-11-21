/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Modules.Frames.FrameBridge
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Nyll.SchemeTheory.Modules.Localization.SectionsLocalizationFiniteCover

/-!
# Basic-open localization of locally trivial module sheaves

Local trivializations transfer scalar localization to module sections. A finite
basic-open refinement then glues numerators and annihilates restriction kernels.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.LocalTrivialization (rM rO rM_rM rO_rO rM_self rO_self
  rM_smul hat_eq le_hat hat_le eApp eInv eInv_eApp eApp_eInv eApp_zero eApp_injective
  restrict_smul_eq eApp_smul unit_map_eq eApp_res ψ ψinv rM_roundtrip rM_roundtrip' rO_roundtrip
  rO_roundtrip' ψ_ψinv ψinv_ψ ψ_injective ψ_zero ψ_smul ψ_res)

open _root_.AlgebraicGeometry.Scheme.Modules (LocProp)

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial

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

namespace LocTriv

variable {X : Scheme.{u}} (M : X.Modules)

section StepA

variable (V : X.Opens) (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)

include V e in
theorem locProp {W : X.Opens} (hW : IsAffineOpen W) (hWV : W ≤ V) (g : Γ(X, W)) : LocProp M W g :=
    by
  have := hW.isLocalization_basicOpen g
  have hDV : X.basicOpen g ≤ V := (X.basicOpen_le g).trans hWV
  constructor
  · intro x
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hax⟩ := IsLocalization.surj (Submonoid.powers g) (ψ M V e hDV x)
    refine ⟨n, ψinv M V e hWV a, ψ_injective M V e hDV ?_⟩
    change ψ M V e hDV (rM M (X.basicOpen_le g) (ψinv M V e hWV a)) = ψ M V e hDV (rO
        (X.basicOpen_le g) (g ^ n) • x)
    rw [ψ_res M V e hWV (X.basicOpen_le g), ψ_ψinv, ψ_smul, mul_comm]
    exact hax.symm
  · intro y hy
    have h0 : algebraMap Γ(X, W) Γ(X, X.basicOpen g) (ψ M V e hWV y) = 0 := by
      change rO (X.basicOpen_le g) (ψ M V e hWV y) = 0
      rw [← ψ_res M V e hWV (X.basicOpen_le g)]
      change ψ M V e hDV (M.presheaf.map (homOfLE (X.basicOpen_le g)).op y) = 0
      rw [hy, ψ_zero]
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers g)] at h0
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := h0
    refine ⟨n, ψ_injective M V e hWV ?_⟩
    rw [ψ_smul, ψ_zero]
    exact hn

end StepA

end LocTriv

open LocTriv in
theorem isLocalization_basicOpen_of_locallyTrivial'
    {X : Scheme.{u}} (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.affineOpens) (f : Γ(X, U.1)) : LocProp M U.1 f := by
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
  let s : Finset Γ(X, U.1) := t.image hOf
  have hs : U.1 ≤ ⨆ h ∈ s, X.basicOpen h := by
    intro p hp
    have := ht hp
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hxt, hpx⟩ := this
    apply Opens.mem_iSup.mpr
    refine ⟨hOf x, Opens.mem_iSup.mpr ⟨Finset.mem_image_of_mem hOf hxt, hpx⟩⟩
  have hmem : ∀ h ∈ s, ∃ x ∈ t, hOf x = h := fun h hh => by simpa [s] using hh
  refine isLocalization_basicOpen_of_finite_basicOpen_cover M U s hs ?_ ?_ f
  · intro h hh g
    obtain ⟨x, -, rfl⟩ := hmem h hh
    exact locProp M (VOf x) (eOf x) (U.2.basicOpen _) (hhV x) g
  · intro h hh h' hh' g
    obtain ⟨x, -, rfl⟩ := hmem h hh
    have haff : IsAffineOpen (X.basicOpen (hOf x) ⊓ X.basicOpen h') := by
      have := (U.2.basicOpen (hOf x)).basicOpen (X.presheaf.map (homOfLE (X.basicOpen_le (hOf
          x))).op h')
      rwa [Scheme.basicOpen_res] at this
    exact locProp M (VOf x) (eOf x) haff (inf_le_left.trans (hhV x)) g

end AlgebraicGeometry.Scheme.Modules

theorem _root_.AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial
    {X : Scheme.{u}} (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.affineOpens) (f : Γ(X, U.1)) : LocProp M U.1 f :=
  AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial' M htriv U f
end Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

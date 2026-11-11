/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Modules.Frames.LocallyFreeBasis
public import Nyll.SchemeTheory.Modules.Localization.SectionLocalization
public import Nyll.SchemeTheory.Modules.LocallyFreeOfRank
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.Topology.Sets.Opens

/-!
# The finite locally free locus of a native module sheaf

A finite basis on an open consists of original sections whose restrictions
are a basis on every smaller open. The union of these actual trivializing
opens is the finite locally free locus. Existing fixed-rank local
trivializations supply such bases without a separate comparison assumption.

If the locus covers the scheme, every affine section module is flat.
The proof uses free sections on smaller basic opens and the original
quasicoherent restriction maps to descend flatness from those localizations.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)

/-- A finite local trivialization given by original sections and their actual restrictions. -/
def IsFiniteFreeOn (U : X.Opens) : Prop :=
  ∃ (n : ℕ) (e : Fin n → Γ(M, U)), ∀ (V : X.Opens) (hVU : V ≤ U),
    ∃ b : Module.Basis (Fin n) Γ(X, V) Γ(M, V),
      ∀ i : Fin n, b i = M.presheaf.map (homOfLE hVU).op (e i)

/-- Restrict the same original finite basis to a smaller open. -/
theorem IsFiniteFreeOn.mono {U V : X.Opens} (hU : IsFiniteFreeOn M U) (hVU : V ≤ U) :
    IsFiniteFreeOn M V := by
  obtain ⟨n, e, he⟩ := hU
  refine ⟨n, fun i => M.presheaf.map (homOfLE hVU).op (e i), ?_⟩
  intro W hWV
  obtain ⟨b, hb⟩ := he W (hWV.trans hVU)
  refine ⟨b, ?_⟩
  intro i
  exact (hb i).trans (congrArg (fun a : Γ(M, U) ⟶ Γ(M, W) => a (e i))
    (M.presheaf.map_comp (homOfLE hVU).op (homOfLE hWV).op))

/-- The original sections on a trivializing open form a free module. -/
theorem IsFiniteFreeOn.moduleFree {U : X.Opens} (hU : IsFiniteFreeOn M U) :
    Module.Free Γ(X, U) Γ(M, U) := by
  obtain ⟨n, e, he⟩ := hU
  obtain ⟨b, _hb⟩ := he U le_rfl
  exact Module.Free.of_basis b

/-- The same actual finite basis proves finiteness of the original sections. -/
theorem IsFiniteFreeOn.moduleFinite {U : X.Opens} (hU : IsFiniteFreeOn M U) :
    Module.Finite Γ(X, U) Γ(M, U) := by
  obtain ⟨n, e, he⟩ := hU
  obtain ⟨b, _hb⟩ := he U le_rfl
  exact Module.Finite.of_basis b

/-- The union of the opens on which the native module has an actual finite local basis. -/
def finiteFreeLocus : X.Opens :=
  ⨆ (U : X.Opens) (_ : IsFiniteFreeOn M U), U

/-- Membership retains an original finite trivializing neighborhood. -/
theorem mem_finiteFreeLocus_iff (x : X) :
    x ∈ finiteFreeLocus M ↔ ∃ U : X.Opens, x ∈ U ∧ IsFiniteFreeOn M U := by
  constructor
  · intro hx
    obtain ⟨U, hU⟩ := Opens.mem_iSup.mp hx
    obtain ⟨hfree, hxU⟩ := Opens.mem_iSup.mp hU
    exact ⟨U, hxU, hfree⟩
  · rintro ⟨U, hxU, hfree⟩
    exact Opens.mem_iSup.mpr ⟨U, Opens.mem_iSup.mpr ⟨hfree, hxU⟩⟩

/-- Existing fixed-rank local trivializations cover the finite locally free locus. -/
theorem finiteFreeLocus_eq_top_of_isLocallyFreeOfRank {n : ℕ}
    (hM : IsLocallyFreeOfRank n M) : finiteFreeLocus M = ⊤ := by
  apply top_unique
  intro x _hx
  obtain ⟨U, hxU, e, he⟩ := hM.exists_basis x
  exact (mem_finiteFreeLocus_iff M x).mpr ⟨U, hxU, n, e, he⟩

/-- On any affine open, actual finite local bases make quasicoherent sections flat. -/
theorem moduleFlat_sections_of_finiteFreeLocus_eq_top [M.IsQuasicoherent]
    (hM : finiteFreeLocus M = ⊤) (U : X.Opens) (hU : IsAffineOpen U) :
    Module.Flat Γ(X, U) Γ(M, U) := by
  have : IsAffine U.toScheme := hU
  have hUqs : IsQuasiSeparated (U : Set X) := by
    apply (isQuasiSeparated_iff_quasiSeparatedSpace (U : Set X) U.2).mpr
    change QuasiSeparatedSpace U.toScheme
    infer_instance
  let s : Set Γ(X, U) := {r | IsFiniteFreeOn M (X.basicOpen r)}
  have hs : Ideal.span s = ⊤ := by
    apply hU.self_le_iSup_basicOpen_iff.mp
    intro x hxU
    have hxM : x ∈ finiteFreeLocus M := by
      rw [hM]
      trivial
    obtain ⟨V, hxV, hV⟩ := (mem_finiteFreeLocus_iff M x).mp hxM
    obtain ⟨r, hrV, hxr⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hxU
    exact Opens.mem_iSup.mpr ⟨⟨r, IsFiniteFreeOn.mono M hV hrV⟩, hxr⟩
  let R : CommRingCat.{u} := Γ(X, U)
  let Rp (r : s) : CommRingCat.{u} := Γ(X, X.basicOpen r.1)
  let σ (r : s) : R →+* Rp r :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r.1)).op).hom
  let (r : s) : Algebra R (Rp r) := (σ r).toAlgebra
  let Mp (r : s) : ModuleCat.{u} (Rp r) := ModuleCat.of (Rp r) Γ(M, X.basicOpen r.1)
  let (r : s) : Module R (Mp r) := Module.compHom (Mp r) (σ r)
  have (r : s) : IsScalarTower R (Rp r) (Mp r) :=
    IsScalarTower.of_compHom R (Rp r) (Mp r)
  have (r : s) : IsLocalization.Away r.1 (Rp r) := hU.isLocalization_basicOpen r.1
  let l (r : s) : Γ(M, U) →ₗ[R] Mp r :=
    (M.val.map (homOfLE (X.basicOpen_le r.1)).op).hom
  have (r : s) : IsLocalizedModule.Away r.1 (l r) :=
    isLocalizedModule_basicOpen_of_isQuasicoherent_of_qcqs M
      hU.isCompact hUqs r.1
  apply Module.flat_of_isLocalized_span (R := R) R Γ(M, U) s hs (fun r => Mp r) l
  intro r
  have : Module.Free (Rp r) (Mp r) := IsFiniteFreeOn.moduleFree M r.property
  have : Module.Flat (Rp r) (Mp r) := inferInstance
  have : Module.Flat R (Rp r) := IsLocalization.flat (Rp r) (Submonoid.powers r.1)
  exact Module.Flat.trans R (Rp r) (Mp r)

end AlgebraicGeometry.Scheme.Modules

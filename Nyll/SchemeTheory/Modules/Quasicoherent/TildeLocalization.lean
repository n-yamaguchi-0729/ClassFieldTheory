/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_iff_isLocalizedModule.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Sheaves.IsIsoOnBasis
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Tactic.Ext
import Nyll.SchemeTheory.Modules.Localization.LocallyTrivialSectionsLocalization

/-!
# Affine modules detected by localization of sections

Characterizes the global-sections comparison by localization on basic open sets.
-/

section isIso_fromTildeGamma_iff_isLocalizedModule

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isIso_fromTildeGamma_iff_isLocalizedModule

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace AlgebraicGeometry.Scheme.Modules

theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_iff_isLocalizedModule {R :
  CommRingCat.{u}}
    (M : (Spec (.of R)).Modules) :
    IsIso M.fromTildeΓ ↔ ∀ f : R, IsLocalizedModule (Submonoid.powers (M := R) f)
      ((modulesSpecToSheaf.obj M).1.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom := by
  let N : (Spec R).Modules := M
  change IsIso N.fromTildeΓ ↔ ∀ f : R, IsLocalizedModule (Submonoid.powers (M := R) f)
    ((modulesSpecToSheaf.obj N).1.map
      (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom
  constructor
  · intro hiso f
    let U := PrimeSpectrum.basicOpen f
    let P : ModuleCat R := ((modulesSpecToSheaf (R := R)).obj N).presheaf.obj (op ⊤)
    let Q : ModuleCat R := ((modulesSpecToSheaf (R := R)).obj N).presheaf.obj (op U)
    let L : ModuleCat R := ((modulesSpecToSheaf (R := R)).obj (tilde P)).presheaf.obj (op U)
    let r : P →ₗ[R] Q := (((modulesSpecToSheaf (R := R)).obj N).1.map
      (homOfLE (le_top : U ≤ ⊤)).op).hom
    let l : P →ₗ[R] L := (tilde.toOpen (R := R) P U).hom
    have : IsIso ((modulesSpecToSheaf (R := R)).map N.fromTildeΓ).1 := by
      have : IsIso ((modulesSpecToSheaf (R := R)).map N.fromTildeΓ) := inferInstance
      exact inferInstanceAs
        (IsIso ((TopCat.Sheaf.forget (ModuleCat R) (Spec R)).map
          ((modulesSpecToSheaf (R := R)).map N.fromTildeΓ)))
    let e : L ≃ₗ[R] Q :=
      (asIso (((modulesSpecToSheaf (R := R)).map N.fromTildeΓ).1.app (op U))).toLinearEquiv
    have happ := Scheme.Modules.toOpen_fromTildeΓ_app N U
    have hre : r = e.toLinearMap ∘ₗ l :=
      (congrArg (fun φ : P ⟶ Q => φ.hom) happ).symm
    have : IsLocalizedModule (Submonoid.powers (M := R) f) l := inferInstance
    change IsLocalizedModule (Submonoid.powers (M := R) f) r
    rw [hre]
    exact IsLocalizedModule.of_linearEquiv (R := R) (Submonoid.powers (M := R) f) l e
  · intro hloc
    suffices IsIso ((modulesSpecToSheaf (R := R)).map N.fromTildeΓ) from
      (SpecModulesToSheafFullyFaithful (R := R)).isIso_of_isIso_map _
    apply TopCat.Sheaf.isIso_of_isIso_app_of_isBasis (B := fun f : R => PrimeSpectrum.basicOpen f)
      PrimeSpectrum.isBasis_basic_opens
    intro f
    let U := PrimeSpectrum.basicOpen f
    let P : ModuleCat R := ((modulesSpecToSheaf (R := R)).obj N).presheaf.obj (op ⊤)
    let Q : ModuleCat R := ((modulesSpecToSheaf (R := R)).obj N).presheaf.obj (op U)
    let L : ModuleCat R := ((modulesSpecToSheaf (R := R)).obj (tilde P)).presheaf.obj (op U)
    let r : P →ₗ[R] Q := (((modulesSpecToSheaf (R := R)).obj N).1.map
      (homOfLE (le_top : U ≤ ⊤)).op).hom
    let l : P →ₗ[R] L := (tilde.toOpen (R := R) P U).hom
    let g : L →ₗ[R] Q :=
      (((modulesSpecToSheaf (R := R)).map N.fromTildeΓ).1.app (op U)).hom
    have : IsLocalizedModule (Submonoid.powers (M := R) f) l := inferInstance
    have : IsLocalizedModule (Submonoid.powers (M := R) f) r := hloc f
    have hg : g ∘ₗ l = r :=
      congrArg (fun φ : P ⟶ Q => φ.hom) (Scheme.Modules.toOpen_fromTildeΓ_app N U)
    let e : L ≃ₗ[R] Q :=
      IsLocalizedModule.linearEquiv (R := R) (Submonoid.powers (M := R) f) l r
    have he' : e.toLinearMap ∘ₗ l = r :=
      LinearMap.ext fun x => IsLocalizedModule.linearEquiv_apply (R := R)
        (Submonoid.powers (M := R) f) l r x
    have he : g = e.toLinearMap :=
      IsLocalizedModule.linearMap_ext (R := R) (S := Submonoid.powers (M := R) f)
        (f := l) (f' := r) (hg.trans he'.symm)
    have hb : Function.Bijective
        (((modulesSpecToSheaf (R := R)).map N.fromTildeΓ).1.app (op U)) := by
      change Function.Bijective g
      rw [he]
      exact e.bijective
    exact (ConcreteCategory.isIso_iff_bijective _).mpr hb
end Scheme_Modules_isIso_fromTildeGamma_iff_isLocalizedModule
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

end isIso_fromTildeGamma_iff_isLocalizedModule

section hom_ext_of_isIso_fromTildeGamma

/-!
# Module morphisms determined by global sections

Detects equality of module morphisms from global sections when the affine comparison is invertible.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_hom_ext_of_isIso_fromTildeGamma

universe u

open CategoryTheory AlgebraicGeometry Opposite

theorem _root_.AlgebraicGeometry.Scheme.Modules.hom_ext_of_isIso_fromTildeGamma {R :
  CommRingCat.{u}}
    {M N : (Spec (.of R)).Modules} [IsIso (Scheme.Modules.fromTildeΓ M)] (φ ψ : M ⟶ N)
    (h : ∀ m : Γ(M, ⊤), φ.app ⊤ m = ψ.app ⊤ m) : φ = ψ := by
  have hΓ : (moduleSpecΓFunctor (R := R)).map φ = (moduleSpecΓFunctor (R := R)).map ψ := by
    ext m
    exact h m
  have n1 := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality φ
  have n2 := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality ψ
  simp only [Functor.comp_map, Functor.id_map] at n1 n2
  rw [← cancel_epi (Scheme.Modules.fromTildeΓ M)]
  change (Scheme.Modules.fromTildeΓNatTrans (R := R)).app M ≫ φ =
    (Scheme.Modules.fromTildeΓNatTrans (R := R)).app M ≫ ψ
  refine n1.symm.trans ?_
  rw [hΓ]
  exact n2
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_hom_ext_of_isIso_fromTildeGamma
end ProofImplementation

end hom_ext_of_isIso_fromTildeGamma

section isIso_fromTildeGamma_of_isLocalization_basicOpen

/-!
# Sheafification from localized global sections

Localization conditions on restrictions to basic opens identify the module sheaf
with the sheaf associated to its global sections on an affine scheme.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace TildeOfLoc

variable {R : CommRingCat.{u}} (M : (Spec (.of R)).Modules)

/-- The `R`-module of sections of `M` over `W`, using the module-valued presheaf on `Spec R`. -/
noncomputable abbrev Γ' (W : (Spec (.of R)).Opens) : ModuleCat R := (modulesSpecToSheaf.obj M).1.obj
    (op W)

/-- The `R`-linear restriction map from global sections to sections over `W`. -/
noncomputable abbrev res' (W : (Spec (.of R)).Opens) : Γ' M ⊤ →ₗ[R] Γ' M W :=
  ((modulesSpecToSheaf.obj M).1.map (homOfLE (le_top : W ≤ ⊤)).op).hom

theorem res'_apply (W : (Spec (.of R)).Opens) (y : Γ(M, ⊤)) :
    res' M W y = (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op) y := rfl

theorem smul_def (W : (Spec (.of R)).Opens) (r : R) (m : Γ' M W) :
    r • m = (((Spec (.of R)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
      ((StructureSheaf.globalSectionsIso R).hom.hom r)) • (show Γ(M, W) from m) := rfl

omit M in
theorem globalSectionsIso_hom_apply (r : R) :
    (StructureSheaf.globalSectionsIso R).hom.hom r = (Scheme.ΓSpecIso (.of R)).inv.hom r := rfl

omit M in
theorem res_top_top (s : Γ(Spec (.of R), ⊤)) :
    ((Spec (.of R)).presheaf.map (homOfLE (le_top : (⊤ : (Spec (.of R)).Opens) ≤ ⊤)).op).hom s = s
        := by
  rw [Subsingleton.elim (homOfLE (le_top : (⊤ : (Spec (.of R)).Opens) ≤ ⊤)) (𝟙 _), op_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- Numerator and kernel conditions for restricting global sections to `W` and clearing denominators
  with powers of `g`. -/
def LocClauses (W : (Spec (.of R)).Opens) (g : Γ(Spec (.of R), ⊤)) : Prop :=
  (∀ x : Γ(M, W), ∃ (n : ℕ) (y : Γ(M, ⊤)),
      M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op y
        = ((Spec (.of R)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (g ^ n) • x)
    ∧ (∀ y : Γ(M, ⊤), M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op y = 0 → ∃ n : ℕ, (g ^ n) • y = 0)

theorem isLocalizedModule_of_locClauses (f : R) (W : (Spec (.of R)).Opens)
    (hunit : IsUnit (algebraMap R (Module.End R (Γ' M W)) f))
    (h : LocClauses M W ((Scheme.ΓSpecIso (.of R)).inv.hom f)) :
    IsLocalizedModule (Submonoid.powers f) (res' M W) := by
  obtain ⟨h1, h2⟩ := h
  refine IsLocalizedModule.mk ?_ ?_ ?_
  · rintro ⟨c, n, rfl⟩
    rw [map_pow]
    exact hunit.pow n
  · intro x
    obtain ⟨n, y, hy⟩ := h1 x
    refine ⟨(y, ⟨f ^ n, n, rfl⟩), ?_⟩
    change (f ^ n) • x = res' M W y
    rw [res'_apply, hy, smul_def, globalSectionsIso_hom_apply, map_pow]
  · intro y₁ y₂ hyy
    have h0 : res' M W (y₁ - y₂) = 0 := by
      rw [map_sub, sub_eq_zero]; exact hyy
    obtain ⟨n, hn⟩ := h2 (y₁ - y₂) h0
    refine ⟨⟨f ^ n, n, rfl⟩, ?_⟩
    change (f ^ n) • y₁ = (f ^ n) • y₂
    rw [← sub_eq_zero, ← smul_sub, smul_def, globalSectionsIso_hom_apply, map_pow, res_top_top]
    exact hn

end TildeOfLoc

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules in
theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_of_isLocalization_basicOpen
    {R : CommRingCat.{u}} (M : (Spec (.of R)).Modules)
    (hloc : ∀ g : Γ(Spec (.of R), ⊤),
      (∀ x : Γ(M, (Spec (.of R)).basicOpen g), ∃ (n : ℕ) (y : Γ(M, ⊤)),
          M.presheaf.map (homOfLE ((Spec (.of R)).basicOpen_le g)).op y
            = ((Spec (.of R)).presheaf.map (homOfLE ((Spec (.of R)).basicOpen_le g)).op).hom (g ^ n)
                • x)
        ∧ (∀ y : Γ(M, ⊤), M.presheaf.map (homOfLE ((Spec (.of R)).basicOpen_le g)).op y = 0 →
            ∃ n : ℕ, (g ^ n) • y = 0)) :
    IsIso M.fromTildeΓ := by
  rw [AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_iff_isLocalizedModule]
  intro f
  have hW : (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv.hom f) = PrimeSpectrum.basicOpen
      f :=
    basicOpen_eq_of_affine (R := .of R) f
  have h : TildeOfLoc.LocClauses M ((Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv.hom f))
      ((Scheme.ΓSpecIso (.of R)).inv.hom f) :=
    hloc _
  rw [hW] at h
  exact TildeOfLoc.isLocalizedModule_of_locClauses M f (PrimeSpectrum.basicOpen f)
    (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (M := M) f le_rfl) h
end Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

end isIso_fromTildeGamma_of_isLocalization_basicOpen

section isIso_fromTildeGamma_of_locallyTrivial

/-!
# Affine comparison for locally trivial modules

Proves that the global-sections comparison is an isomorphism for locally trivial modules.
-/

/-! The tilde comparison is an isomorphism for locally trivial modules. -/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isIso_fromTildeGamma_of_locallyTrivial

universe u

open CategoryTheory AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial
    {R : CommRingCat.{u}} (M : (Spec (.of R)).Modules)
    (htriv : ∀ x : Spec (.of R), ∃ (V : (Spec (.of R)).Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit
        V.toScheme.ringCatSheaf)) :
    IsIso M.fromTildeΓ :=
  AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_of_isLocalization_basicOpen M fun g =>
    AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial M htriv
      ⟨⊤, isAffineOpen_top (Spec (.of R))⟩ g
end Scheme_Modules_isIso_fromTildeGamma_of_locallyTrivial
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

end isIso_fromTildeGamma_of_locallyTrivial

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_isFinite.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Modules.Frames.FrameBridge
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.SchemeTheory.Modules.ProjectivePresentation.ProjectivePresentation
public import Nyll.SchemeTheory.Modules.Localization.LocallyTrivialSectionsLocalization
public import Nyll.SchemeTheory.Modules.Frames.ProjectivePresentationFromFrames

/-!
# Scheme Modules Finite By Sections of is Finite
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.LocalTrivialization (rM rO rM_rM rO_rO rM_self rO_self
  rM_smul hat_eq le_hat hat_le eApp eInv eInv_eApp eApp_eInv eApp_zero eApp_injective
  restrict_smul_eq eApp_smul unit_map_eq eApp_res ψ ψinv rM_roundtrip rM_roundtrip' rO_roundtrip
  rO_roundtrip' ψ_ψinv ψinv_ψ ψ_injective ψ_zero ψ_smul ψ_res)

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_FiniteBySections_of_isFinite

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace
open _root_.Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace FBSFinite
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

section Frames


variable {X : Scheme.{u}} (M : X.Modules) (V : X.Opens)
  (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)

theorem eq_of_le_bot {W : X.Opens} (hW : W ≤ ⊥) (s t : Γ(M, W)) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X.carrier)
    (fun _ : Empty => (⊥ : X.Opens)) W (fun i => i.elim) (hW.trans bot_le) s t (fun i => i.elim)

theorem frame_of_eq_unit_smul {W : X.Opens} (hWV : W ≤ V) (y : Γ(M, ⊤)) (c : Γ(X, W)) (hc : IsUnit
  c)
    (hy : rM M (le_top : W ≤ ⊤) y = c • ψinv M V e hWV 1) (V' : X.Opens) (hV' : V' ≤ W) :
    Function.Bijective fun a : Γ(X, V') => a • (M.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op y)
      := by
  have hcu : IsUnit (rO hV' c) := hc.map _
  have h1 : rM M hV' (ψinv M V e hWV 1) = ψinv M V e (hV'.trans hWV) 1 := by
    apply ψ_injective M V e (hV'.trans hWV)
    rw [ψ_res M V e hWV hV', ψ_ψinv, ψ_ψinv]
    exact map_one _
  have hres : M.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op y = rO hV' c • ψinv M V e (hV'.trans
    hWV) 1 := by
    change rM M le_top y = _
    rw [← rM_rM M (le_top : W ≤ ⊤) hV', hy, rM_smul, h1]
  have key : (fun a : Γ(X, V') => a • (M.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op y))
      = (ψinv M V e (hV'.trans hWV)) ∘ (fun a => a * rO hV' c) := by
    funext a
    simp only [Function.comp_apply]
    rw [hres, ← mul_smul]
    apply ψ_injective M V e (hV'.trans hWV)
    rw [ψ_smul, ψ_ψinv, ψ_ψinv, mul_one]
  rw [key]
  refine Function.Bijective.comp ?_ ?_
  · exact Function.bijective_iff_has_inverse.mpr ⟨ψ M V e _, ψ_ψinv M V e _, ψinv_ψ M V e _⟩
  · exact (Units.mulRight hcu.unit).bijective

end Frames

theorem main {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsFinite f]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Scheme.Modules.FiniteBySections M f := by
  classical
  have : IsAffine X := isAffine_of_isAffineHom f
  have htop : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  have hpt : ∀ x : X, ∃ (g : Γ(X, ⊤)) (y : Γ(M, ⊤)), x ∈ X.basicOpen g ∧
      ∀ V' : X.Opens, V' ≤ X.basicOpen g →
        Function.Bijective fun a : Γ(X, V') => a • (M.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op
          y) := by
    intro x
    obtain ⟨V, hxV, ⟨e0⟩⟩ := hM.exists_trivialization x
    let e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf :=
      (restrictFunctorIsoPullback V.ι).app M ≪≫ e0
    obtain ⟨g, hgV, hxg⟩ := htop.exists_basicOpen_le ⟨x, hxV⟩ (Set.mem_univ x)
    obtain ⟨n, y, hy⟩ := (isLocalization_basicOpen_of_locallyTrivial M hM.exists_trivialization
      ⟨⊤, htop⟩ g).1
      (ψinv M V e hgV 1)
    refine ⟨g, y, hxg, frame_of_eq_unit_smul M V e hgV y _ ?_ hy⟩
    rw [map_pow]
    exact (RingedSpace.isUnit_res_basicOpen _ g).pow n
  choose g y hxg hfr using hpt
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (X.basicOpen (g x) : Set X))
    (fun x => (X.basicOpen (g x)).2) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxg x⟩)
  let l : List X := t.toList
  let N : ℕ := l.length
  let σ : Fin (N + 1) → Γ(M, ⊤) := fun i => Fin.cases (0 : Γ(M, ⊤)) (fun k => y (l.get k)) i
  let U : Fin (N + 1) → X.Opens := fun i => Fin.cases (⊥ : X.Opens) (fun k => X.basicOpen (g
    (l.get k))) i
  have hU : iSup U = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    have hx := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx
    obtain ⟨x0, hx0t, hx0⟩ := hx
    have hx0l : x0 ∈ l := Finset.mem_toList.mpr hx0t
    obtain ⟨k, hk⟩ := List.get_of_mem hx0l
    refine Opens.mem_iSup.mpr ⟨k.succ, ?_⟩
    change x ∈ (Fin.cases (⊥ : X.Opens) (fun k => X.basicOpen (g (l.get k))) k.succ : X.Opens)
    rw [Fin.cases_succ, hk]
    exact hx0
  have hframe : ∀ (i : Fin (N + 1)) (V' : X.Opens), V' ≤ U i →
      Function.Bijective fun a : Γ(X, V') => a • (M.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op (σ
        i)) := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · intro V' hV'
      have hV'b : V' ≤ ⊥ := hV'
      have : Subsingleton Γ(X, V') :=
        CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty (le_bot_iff.mp hV'b))
      exact ⟨fun a b _ => Subsingleton.elim a b, fun m => ⟨0, eq_of_le_bot M hV'b _ _⟩⟩
    · intro V' hV'
      exact hfr (l.get k) V' hV'
  obtain ⟨𝔓, -, -⟩ := exists_projPresentation_of_iSup_eq_top f M N σ U hU hframe
  refine ⟨N, 𝔓, ?_⟩
  have : IsFinite (𝔓.toProj ≫ ProjSpace.π R N) := by rw [𝔓.toProj_π]; infer_instance
  exact IsFinite.of_comp 𝔓.toProj (ProjSpace.π R N)

end AlgebraicGeometry.Scheme.Modules.FBSFinite

theorem _root_.AlgebraicGeometry.Scheme.Modules.FiniteBySections.of_isFinite {R : Type u}
  [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsFinite f]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Scheme.Modules.FiniteBySections M f :=
  AlgebraicGeometry.Scheme.Modules.FBSFinite.main f M hM
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_FiniteBySections_of_isFinite
end ProofImplementation

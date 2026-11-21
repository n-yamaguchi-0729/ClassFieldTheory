/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Util.WithWeakNamespace
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.Localization.Away.Basic
public import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverOf

/-!
# Degree-zero exactness of the affine-cover Cech complex

Sections on an open are exactly the degree-zero cochains whose Cech differential vanishes.
The increasing-index construction is compared with the finite-subset description.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug

open _root_.AlgebraicGeometry
open _root_.CategoryTheory
open _root_.TopologicalSpace
open _root_.Opposite

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace OrderedAffineCoverOf
open _root_.AlgebraicGeometry.Scheme.OrderedAffineCoverOf
namespace Acyclic
open _root_.AlgebraicGeometry.Scheme.OrderedAffineCoverOf
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

universe u
section ResHelpers

variable {V : Scheme.{u}}

theorem res_refl {O : V.Opens} (h : O ≤ O) (x : Γ(V, O)) :
    (V.presheaf.map (homOfLE h).op).hom x = x := by
  have : (homOfLE h : O ⟶ O) = 𝟙 O := rfl
  rw [this, op_id, V.presheaf.map_id]; rfl

theorem res_res {O₁ O₂ O₃ : V.Opens} (h12 : O₁ ≤ O₂) (h23 : O₂ ≤ O₃)
    (x : Γ(V, O₃)) :
    (V.presheaf.map (homOfLE h12).op).hom ((V.presheaf.map (homOfLE h23).op).hom x)
      = (V.presheaf.map (homOfLE (h12.trans h23)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]; rfl

theorem altC_at_eq {W : V.Opens} {K : Scheme.OrderedAffineCoverOf W}
    {n : ℕ} (z : K.cochain n) {σ τ : K.Idx n} (h : σ = τ)
    {O : V.Opens} (hσ : O ≤ K.inter σ) (hτ : O ≤ K.inter τ) :
    (V.presheaf.map (homOfLE hσ).op).hom (z σ)
      = (V.presheaf.map (homOfLE hτ).op).hom (z τ) := by
  subst h; rfl

end ResHelpers

section Idx0
variable {V : Scheme.{u}} {W : V.Opens} (K : Scheme.OrderedAffineCoverOf W) (i₀ : K.ι)

/-- The degree-zero Cech index determined by a single cover member. -/
def idx0 : K.Idx 0 :=
  ⟨fun _ => i₀, fun a b h => absurd (Subsingleton.elim (α := Fin 1) a b) (ne_of_lt h)⟩
end Idx0

section Acyclic0

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))
variable {W : V.Opens} (K : Scheme.OrderedAffineCoverOf W)
include π

theorem affine_acyclic₀ :
    letI := Scheme.OrderedAffineCoverOf.moduleSections π
    LinearMap.ker (K.d π 0) = LinearMap.range (K.aug π) := by
  let := Scheme.OrderedAffineCoverOf.moduleSections π
  refine le_antisymm (fun z hz => ?_) ?_
  · have hcov : W ≤ ⨆ σ : K.Idx 0, K.inter σ := by
      refine K.iSup_eq.ge.trans (iSup_le fun i => ?_)
      exact le_iSup_of_le (idx0 K i) (le_iInf fun _ => le_rfl)
    have hcore : ∀ (a b : K.ι), a < b → ∀ (σ τ : K.Idx 0),
        σ.1 0 = a → τ.1 0 = b → ∀ {O : V.Opens}
        (hOσ : O ≤ K.inter σ) (hOτ : O ≤ K.inter τ),
        O ≤ K.U a ⊓ K.U b →
        (V.presheaf.map (homOfLE hOσ).op).hom (z σ)
          = (V.presheaf.map (homOfLE hOτ).op).hom (z τ) := by
      intro a b hab σ τ hσ hτ O hOσ hOτ hOab
      let ρ : K.Idx 1 := ⟨![a, b], by
        intro c d hcd
        fin_cases c <;> fin_cases d
        · exact (Nat.lt_irrefl 0 hcd).elim
        · exact hab
        · exact (Nat.not_lt_zero 1 hcd).elim
        · exact (Nat.lt_irrefl 1 hcd).elim⟩
      have hρ0 : K.face ρ 0 = τ := altIdx_eq_of_altImg K
        (by rw [altImg_deg0, altImg_deg0, hτ]; rfl)
      have hρ1 : K.face ρ 1 = σ := altIdx_eq_of_altImg K
        (by rw [altImg_deg0, altImg_deg0, hσ]; rfl)
      have hOρ : O ≤ K.inter ρ :=
        le_iInf fun j => by fin_cases j
                            · exact hOab.trans inf_le_left
                            · exact hOab.trans inf_le_right
      have hker := congrFun (LinearMap.mem_ker.mp hz) ρ
      rw [Scheme.OrderedAffineCoverOf.d_apply, Fin.sum_univ_two] at hker
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul,
        Pi.zero_apply, add_neg_eq_zero] at hker
      have key := congrArg (V.presheaf.map (homOfLE hOρ).op).hom hker
      rw [res_res, res_res,
        altC_at_eq z hρ0 _ hOτ,
        altC_at_eq z hρ1 _ hOσ] at key
      exact key.symm
    have hcompat : TopCat.Presheaf.IsCompatible V.sheaf.1
        (K.inter (i := 0)) z := by
      intro σ τ
      have hOab : K.inter σ ⊓ K.inter τ
          ≤ K.U (σ.1 0) ⊓ K.U (τ.1 0) :=
        inf_le_inf (iInf_le _ 0) (iInf_le _ 0)
      rcases lt_trichotomy (σ.1 0) (τ.1 0) with h | h | h
      · exact hcore _ _ h σ τ rfl rfl inf_le_left inf_le_right hOab
      · have heq : σ = τ := altIdx_eq_of_altImg K
          (by rw [altImg_deg0, altImg_deg0, h])
        subst heq; rfl
      · exact (hcore _ _ h τ σ rfl rfl inf_le_right inf_le_left
          (hOab.trans (inf_comm _ _).le)).symm
    obtain ⟨w, hw, -⟩ := V.sheaf.existsUnique_gluing' (K.inter (i := 0)) W
      (fun σ => homOfLE (K.inter_le_base σ)) hcov z hcompat
    exact ⟨w, funext fun σ => hw σ⟩
  · rintro _ ⟨w, rfl⟩
    refine LinearMap.mem_ker.mpr (funext fun τ => ?_)
    rw [Scheme.OrderedAffineCoverOf.d_apply, Fin.sum_univ_two]
    simp only [Scheme.OrderedAffineCoverOf.aug, LinearMap.pi_apply,
        Scheme.OrderedAffineCoverOf.res_apply,
      res_res, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
      neg_one_smul, Pi.zero_apply, add_neg_cancel]

end Acyclic0

end AlgebraicGeometry.Scheme.OrderedAffineCoverOf.Acyclic

end

universe u

with_weak_namespace _root_.AlgebraicCurves.Geometry.Schemes.Proofs
open _root_.AlgebraicGeometry
    Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug.AlgebraicGeometry in
with_weak_namespace Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug
theorem _root_.AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug {R : Type
    u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) {W : V.Opens}
    (K : V.OrderedAffineCoverOf W) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections π
    LinearMap.ker (K.d π 0) = LinearMap.range (K.aug π) :=
  Scheme.OrderedAffineCoverOf.Acyclic.affine_acyclic₀ π K
end Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation

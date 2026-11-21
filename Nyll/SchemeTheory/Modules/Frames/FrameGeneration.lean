/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Modules.Frames.FrameBridge

/-! # Local generation by a section -/

@[expose] public section

open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.LocalTrivialization

universe u

variable {X : Scheme.{u}} (M : X.Modules)

/-- The local frame corresponding to the unit coordinate of a trivialization. -/
noncomputable def frame (V : X.Opens)
    (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) : Γ(M, V) :=
  ψinv M V e le_rfl 1

section

variable (V : X.Opens) (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)

theorem ψ_frame : ψ M V e le_rfl (frame M V e) = 1 := ψ_ψinv M V e le_rfl 1

theorem ψ_rM_frame {W : X.Opens} (hWV : W ≤ V) :
    ψ M V e hWV (rM M hWV (frame M V e)) = 1 := by
  have h := ψ_res M V e le_rfl hWV (frame M V e)
  have hOne : rO hWV (1 : Γ(X, V)) = 1 := map_one _
  rw [ψ_frame, hOne] at h
  exact h

theorem eq_smul_frame {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, W)) :
    m = ψ M V e hWV m • rM M hWV (frame M V e) := by
  apply ψ_injective M V e hWV
  rw [ψ_smul, ψ_rM_frame, mul_one]

end

/-- A section generates each smaller open containing the given point. -/
def IsGeneratorAt (U : X.Opens) (s : Γ(M, U)) (y : X) : Prop :=
  ∀ (W : X.Opens) (h : W ≤ U), y ∈ W → ∀ m : Γ(M, W), ∃ a : Γ(X, W), m = a • rM M h s

/-- The frame from a trivialization generates on every smaller open. -/
theorem isGeneratorAt_frame (V : X.Opens)
    (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) (y : X) :
    IsGeneratorAt M V (frame M V e) y :=
  fun _ h _ m => ⟨ψ M V e h m, eq_smul_frame M V e h m⟩

/-- Restricting a generator preserves its local generation at the point. -/
theorem isGeneratorAt_rM {U W : X.Opens} (h : W ≤ U) (s : Γ(M, U)) (y : X)
    (hs : IsGeneratorAt M U s y) :
    IsGeneratorAt M W (rM M h s) y := by
  intro W' h' hyW' m
  obtain ⟨a, ha⟩ := hs W' (h'.trans h) hyW' m
  refine ⟨a, ?_⟩
  rw [rM_rM]
  exact ha

end AlgebraicGeometry.Scheme.Modules.LocalTrivialization

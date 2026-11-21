/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Modules.Frames.FrameBridge
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Nyll.SchemeTheory.Modules.Frames.Frames

/-!
# Frames obtained from a pullback trivialization

A trivialization on an open subscheme gives compatible local generators and a section
that is a frame on that open.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A pullback trivialization on an open subset supplies a frame. -/
theorem exists_isFrameOn_of_pullback_iso_unit {X : Scheme.{u}} {M : X.Modules} (U : X.Opens)
    (eU : (pullback U.ι).obj M ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    ∃ s : Γ(M, U), IsFrameOn s U := by
  let e : (FrameBridge.restrictFunctor' U).obj M ≅
      SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf :=
    (FrameBridge.restrictFunctor'IsoPullback U).app M ≪≫ eU
  let D := FrameBridge.trivializationBelow M e
  refine ⟨D.gen (𝟙 (Opposite.op U)), ?_⟩
  intro W hWU _
  have hc : M.presheaf.map (homOfLE hWU).op (D.gen (𝟙 (Opposite.op U))) = D.gen (homOfLE hWU).op :=
      by
    have h := D.compat (𝟙 (Opposite.op U)) (homOfLE hWU).op
    rw [Category.id_comp] at h
    exact h
  simp only [hc]
  exact D.bij (homOfLE hWU).op


/-- An invertible module has a frame on a neighborhood of each point. -/
theorem IsInvertible.exists_isFrameOn {X : Scheme.{u}} {M : X.Modules}
    (hM : IsInvertible M) (x : X) :
    ∃ (U : X.Opens) (s : Γ(M, U)), x ∈ U ∧ IsFrameOn s U := by
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hM.1 x
  obtain ⟨s, hs⟩ := exists_isFrameOn_of_pullback_iso_unit U eU
  exact ⟨U, s, hxU, hs⟩

end AlgebraicGeometry.Scheme.Modules

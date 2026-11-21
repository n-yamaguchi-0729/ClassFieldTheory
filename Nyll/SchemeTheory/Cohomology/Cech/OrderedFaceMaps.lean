/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_d_comp_d.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Data.Fin.SuccPred

/-! # Composition identities for ordered Čech face maps -/

@[expose] public section

/-- The two composites omitting the same ordered pair of indices are equal. -/
theorem Fin.succAbove_comp_succAbove_of_le {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j) :
    Fin.succAbove j.succ ∘ Fin.succAbove i = Fin.succAbove i.castSucc ∘ Fin.succAbove j := by
  funext k
  have hj : i.castSucc.succAbove j = j.succ :=
    Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr h)
  simpa only [Function.comp_apply, hj, Fin.predAbove_castSucc_of_le j i h] using
    Fin.succAbove_succAbove_succAbove_predAbove i.castSucc j k

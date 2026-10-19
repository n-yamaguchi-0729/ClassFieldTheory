/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_of_isPullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
/-! A Cartesian square identifies the iterated pullbacks of schemes and their modules. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open AlgebraicGeometry.Scheme.Modules

theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_of_isPullback
    {X T X' W' Z : Scheme.{u}} (π : X ⟶ T) (π' : X' ⟶ W') (g' : X' ⟶ X) (j : W' ⟶ T)
    (hcart : IsPullback g' π' π j) (s : Z ⟶ W') :
    ∃ φ : Limits.pullback π (s ≫ j) ≅ Limits.pullback π' s,
      φ.hom ≫ Limits.pullback.snd π' s = Limits.pullback.snd π (s ≫ j) ∧
      φ.hom ≫ Limits.pullback.fst π' s ≫ g' = Limits.pullback.fst π (s ≫ j) ∧
      ∀ G : X.Modules, Nonempty ((Scheme.Modules.pullback (Limits.pullback.fst π (s ≫ j))).obj G ≅
        (Scheme.Modules.pullback φ.hom).obj
          ((Scheme.Modules.pullback (Limits.pullback.fst π' s)).obj ((Scheme.Modules.pullback
              g').obj G))) := by
  have hbig : IsPullback (Limits.pullback.fst π' s ≫ g') (Limits.pullback.snd π' s) π (s ≫ j) :=
    (IsPullback.of_hasPullback π' s).paste_horiz hcart
  let φ : Limits.pullback π (s ≫ j) ≅ Limits.pullback π' s :=
    (IsPullback.of_hasPullback π (s ≫ j)).isoIsPullback _ _ hbig
  have hφ₁ : φ.hom ≫ Limits.pullback.fst π' s ≫ g' = Limits.pullback.fst π (s ≫ j) :=
    IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hφ₂ : φ.hom ≫ Limits.pullback.snd π' s = Limits.pullback.snd π (s ≫ j) :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  refine ⟨φ, hφ₂, hφ₁, fun G => ⟨?_⟩⟩
  exact (pullbackCongr hφ₁.symm).app G ≪≫ (pullbackComp _ _).symm.app G ≪≫
    (Scheme.Modules.pullback φ.hom).mapIso ((pullbackComp _ _).symm.app G)

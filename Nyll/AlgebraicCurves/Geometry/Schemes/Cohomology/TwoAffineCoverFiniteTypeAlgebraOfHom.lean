/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finiteType_algebraOfHom.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover

/-! A finite type scheme morphism gives a finite type algebra on each affine open. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.finiteType_algebraOfHom
    {R : Type u} [CommRing R] {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) [LocallyOfFiniteType t]
    (W : T.Opens) (hW : IsAffineOpen W) :
    let _ : Algebra R Γ(T, W) := Scheme.TwoAffineOpenCover.algebraOfHom t W
    Algebra.FiniteType R Γ(T, W) := by
  intro algebraStructure
  have h : (t.appLE ⊤ W le_top).hom.FiniteType :=
    t.finiteType_appLE (isAffineOpen_top _) hW le_top
  have h' : (Scheme.ΓSpecIso (.of R)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (.of
        R)).symm.commRingCatIsoToRingEquiv.surjective
  rw [← RingHom.finiteType_algebraMap]
  exact h.comp h'

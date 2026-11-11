/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_smooth_isSeparated_quasiCompact_geometricallyConnected_of_finiteEtale_baseChange.lean
Also adapted from the geometric-connectedness descent proof:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.CategoryTheory.MorphismProperty.Descent

/-! # Geometric connectedness descends along surjective base changes

Extracted from the finite-etale curve descent supplier; the proof itself only
requires surjectivity and works for arbitrary scheme morphisms.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A surjective base change detects geometrically connected fibres. -/
theorem GeometricallyConnected.of_pullback_snd {X S S' : Scheme.{u}} (f : X ⟶ S) (σ : S' ⟶ S)
  [Surjective σ]
    [hgc : GeometricallyConnected (pullback.snd f σ)] : GeometricallyConnected f := by
  refine ⟨fun K _ k Z a b hZ => ?_⟩
  obtain ⟨z, -⟩ := (pullback.fst k σ).surjective default
  let ι := (pullback k σ).fromSpecResidueField z
  let kL : Spec ((pullback k σ).residueField z) ⟶ Spec (.of K) := ι ≫ pullback.fst k σ
  let l' : Spec ((pullback k σ).residueField z) ⟶ S' := ι ≫ pullback.snd k σ
  have hkl : kL ≫ k = l' ≫ σ := by simp only [kL, l', Category.assoc, pullback.condition]
  have : Surjective kL := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  have s : IsPullback (pullback.fst b kL ≫ a) (pullback.snd b kL) f (l' ≫ σ) := by
    rw [← hkl]
    exact (IsPullback.of_hasPullback b kL).paste_horiz hZ
  let m : pullback b kL ⟶ pullback f σ :=
    pullback.lift (pullback.fst b kL ≫ a) (pullback.snd b kL ≫ l')
      (by simpa only [Category.assoc] using s.w)
  have hm₁ : m ≫ pullback.fst f σ = pullback.fst b kL ≫ a := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd f σ = pullback.snd b kL ≫ l' := pullback.lift_snd _ _ _
  have s' : IsPullback (m ≫ pullback.fst f σ) (pullback.snd b kL) f (l' ≫ σ) := by rw [hm₁]; exact s
  have sq : IsPullback m (pullback.snd b kL) (pullback.snd f σ) l' :=
    IsPullback.of_right s' hm₂ (IsPullback.of_hasPullback f σ)
  have hc : ConnectedSpace ↥(pullback b kL) := hgc.geometrically_connectedSpace l' m (pullback.snd
    b kL) sq
  exact (pullback.fst b kL).surjective.connectedSpace (pullback.fst b kL).continuous


/-- Geometric connectedness is a property that descends along all surjective morphisms. -/
instance GeometricallyConnected.descendsAlong_surjective :
    MorphismProperty.DescendsAlong (@GeometricallyConnected : MorphismProperty Scheme.{u})
      (@Surjective : MorphismProperty Scheme.{u}) where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    have : Surjective f := hf
    have : MorphismProperty.RespectsIso
        (@GeometricallyConnected : MorphismProperty Scheme.{u}) := by
      rw [GeometricallyConnected.eq_geometrically, geometrically_eq_universally]
      exact MorphismProperty.universally_respectsIso _
    have : GeometricallyConnected (pullback.snd g f) := by
      apply (MorphismProperty.cancel_left_of_respectsIso (@GeometricallyConnected)
        h.flip.isoPullback.hom (pullback.snd g f)).mp
      rw [h.flip.isoPullback_hom_snd]
      exact hfst
    exact GeometricallyConnected.of_pullback_snd g f

end AlgebraicGeometry

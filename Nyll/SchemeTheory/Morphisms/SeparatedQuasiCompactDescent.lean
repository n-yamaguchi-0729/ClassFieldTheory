/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_smooth_isSeparated_quasiCompact_geometricallyConnected_of_finiteEtale_baseChange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Separatedness and quasi-compactness under flat or surjective descent

These generic proofs are extracted from the attributed finite-étale base-change
supplier, so they can be used by scheme-theoretic foundations without curve imports.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Quasi-compactness is local on the target; reuse the canonical Mathlib proof. -/
theorem QuasiCompact.isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u}) :=
  (HasAffineProperty.iff.mp
    instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat).1

attribute [local instance] universallyClosed_respectsIso

/-- A separated morphism is characterized by universal closedness of its diagonal. -/
theorem IsSeparated.iff_universallyClosed_diagonal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsSeparated f ↔ UniversallyClosed (pullback.diagonal f) := by
  refine ⟨fun _ => inferInstance, fun _ => ⟨?_⟩⟩
  exact IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal f).isClosedMap.isClosed_range

/-- Separatedness is the diagonal of universal closedness as a morphism property. -/
theorem IsSeparated.eq_diagonal_universallyClosed :
    @IsSeparated = MorphismProperty.diagonal (@UniversallyClosed : MorphismProperty Scheme.{u}) :=
      by
  ext X Y f
  exact IsSeparated.iff_universallyClosed_diagonal f

/-- Separatedness descends under a faithfully flat quasi-compact cover. -/
theorem IsSeparated.descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@IsSeparated : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have : MorphismProperty.DescendsAlong
      (@_root_.AlgebraicGeometry.UniversallyClosed : MorphismProperty Scheme.{u})
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Flat ⊓
        @_root_.AlgebraicGeometry.QuasiCompact) :=
    _root_.AlgebraicGeometry.descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact
  have : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.UniversallyClosed : MorphismProperty Scheme.{u}) :=
    _root_.AlgebraicGeometry.universallyClosed_respectsIso
  have : MorphismProperty.IsStableUnderBaseChange
      (@_root_.AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u}) := inferInstance
  have : MorphismProperty.IsStableUnderBaseChange
      (@_root_.AlgebraicGeometry.Flat : MorphismProperty Scheme.{u}) :=
    _root_.AlgebraicGeometry.Flat.isStableUnderBaseChange
  have : MorphismProperty.IsStableUnderBaseChange
      (@_root_.AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u}) :=
    _root_.AlgebraicGeometry.quasiCompact_isStableUnderBaseChange
  have : MorphismProperty.IsStableUnderBaseChange
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Flat :
        MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
      (P := @_root_.AlgebraicGeometry.Surjective) (Q := @_root_.AlgebraicGeometry.Flat)
  have : MorphismProperty.IsStableUnderBaseChange
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Flat ⊓
        @_root_.AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
      (P := @_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Flat)
      (Q := @_root_.AlgebraicGeometry.QuasiCompact)
  rw [IsSeparated.eq_diagonal_universallyClosed]
  have diagonal_descent (P Q : MorphismProperty Scheme.{u})
      [MorphismProperty.DescendsAlong P Q] [MorphismProperty.RespectsIso P]
      [MorphismProperty.IsStableUnderBaseChange Q] :
      MorphismProperty.DescendsAlong (MorphismProperty.diagonal P) Q := inferInstance
  exact diagonal_descent @_root_.AlgebraicGeometry.UniversallyClosed
    (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Flat ⊓
      @_root_.AlgebraicGeometry.QuasiCompact)

/-- Quasi-compactness descends under a surjective quasi-compact base change. -/
theorem QuasiCompact.of_pullback_snd {X S S' : Scheme.{u}} (f : X ⟶ S) (σ : S' ⟶ S) [Surjective σ]
    [QuasiCompact σ] [hq : QuasiCompact (pullback.snd f σ)] : QuasiCompact f := by
  refine ⟨fun U hUo hUc => ?_⟩
  have h1 : IsCompact ((pullback.snd f σ) ⁻¹' (σ ⁻¹' U)) :=
    QuasiCompact.isCompact_preimage _ (hUo.preimage σ.continuous) (QuasiCompact.isCompact_preimage
      _ hUo hUc)
  have h2 : (pullback.fst f σ) '' ((pullback.snd f σ) ⁻¹' (σ ⁻¹' U)) = f ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      change f (pullback.fst f σ z) ∈ U
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      exact hz
    · intro hx
      obtain ⟨s', hs'⟩ := σ.surjective (f x)
      obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := σ) x s'
        hs'.symm
      refine ⟨z, ?_, hz1⟩
      change σ (pullback.snd f σ z) ∈ U
      rw [hz2, hs']
      exact hx
  rw [← h2]
  exact h1.image (pullback.fst f σ).continuous


/-- Quasi-compactness descends under a faithfully flat quasi-compact cover. -/
theorem QuasiCompact.descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@QuasiCompact : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    have : Surjective f := hf.1.1
    have : QuasiCompact f := hf.2
    have : QuasiCompact (pullback.snd g f) := by
      have : QuasiCompact fst := hfst
      have hq : QuasiCompact (h.flip.isoPullback.inv ≫ fst) := inferInstance
      rw [h.flip.isoPullback_inv_snd] at hq
      exact hq
    exact QuasiCompact.of_pullback_snd g f


end AlgebraicGeometry

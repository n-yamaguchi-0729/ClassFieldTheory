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

module

public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange

/-!
The pullback square associated with baseChangeSnd along a relative scheme morphism.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Picard.Proofs.IsPullback_baseChangeSnd

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra

theorem _root_.AlgebraicGeometry.RelPicard.isPullback_baseChangeSnd
    {R : Type u} [CommRing R] {C T T' : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    IsPullback (baseChangeSnd c ψ) (pullback.snd c t') (pullback.snd c t) ψ.1 := by
  refine IsPullback.of_right (h₁₂ := pullback.fst c t) (v₁₃ := c) (h₂₂ := t) ?_
    (RelPicard.BaseChange.baseChangeSnd_snd' (cc := c) (ψ := ψ)) (IsPullback.of_hasPullback c t)
  rw [RelPicard.BaseChange.baseChangeSnd_fst' (cc := c) (ψ := ψ), ψ.2]
  exact IsPullback.of_hasPullback c t'

/-- Base change along the same family preserves a pullback square over the base. -/
theorem _root_.AlgebraicGeometry.RelPicard.isPullback_baseChangeSnd_of_isPullback
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {X U V W : Scheme.{u}} {x : X ⟶ Spec (CommRingCat.of R)}
    {uS : U ⟶ Spec (CommRingCat.of R)} {vS : V ⟶ Spec (CommRingCat.of R)}
    {wS : W ⟶ Spec (CommRingCat.of R)}
    (u : SchemeHomOver uS x) (v : SchemeHomOver vS x)
    (a : SchemeHomOver wS uS) (b : SchemeHomOver wS vS)
    (h : IsPullback a.1 b.1 u.1 v.1) :
    IsPullback (baseChangeSnd c a) (baseChangeSnd c b) (baseChangeSnd c u) (baseChangeSnd c v) := by
  have hbig : IsPullback (pullback.snd c wS ≫ a.1) (baseChangeSnd c b) u.1
      (pullback.snd c vS ≫ v.1) :=
    (RelPicard.isPullback_baseChangeSnd c b).flip.paste_horiz h
  have hbig' : IsPullback (baseChangeSnd c a ≫ pullback.snd c uS) (baseChangeSnd c b) u.1
      (baseChangeSnd c v ≫ pullback.snd c x) := by
    rw [show baseChangeSnd c a ≫ pullback.snd c uS = pullback.snd c wS ≫ a.1
        from pullback.lift_snd _ _ _,
      show baseChangeSnd c v ≫ pullback.snd c x = pullback.snd c vS ≫ v.1
        from pullback.lift_snd _ _ _]
    exact hbig
  refine hbig'.of_right ?_ (RelPicard.isPullback_baseChangeSnd c u).flip
  rw [baseChangeSnd_comp, baseChangeSnd_comp]
  congr 1
  exact Subtype.ext h.w
end AlgebraicCurves.Geometry.Picard.Proofs.IsPullback_baseChangeSnd
end ProofImplementation

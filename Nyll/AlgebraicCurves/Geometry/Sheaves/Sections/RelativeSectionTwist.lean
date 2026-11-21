/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelPicardThetaBundle.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.IdealSheafModule
public import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal

/-!
# Twists by a rigidifying section

Defines the ideal and module twists of the rigidifying section after base change.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra MonoidalCategory

namespace AlgebraicGeometry.RelPicard

section RigidifyingSection

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {T : Scheme.{u}} (t : T ⟶ Spec
    (CommRingCat.of R))

/-- The ideal sheaf of the rigidifying section after base change. -/
def sectionIdeal : (pullback c t).IdealSheafData := (rigSection c t ε).ker

/-- The inverse ideal module of the rigidifying section raised to the given power. -/
def sectionTwist (r : ℕ) : (pullback c t).Modules := ((sectionIdeal c ε t) ^ r).invModule

/-- The pullback of a module to the fibre over the given field-valued point. -/
abbrev fibreModule {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (F : (pullback c t).Modules) : (pullback (pullback.snd c t) s).Modules :=
  (Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj F

end RigidifyingSection

section FibreIso

variable {R : Type u} [CommRing R]
  {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R))
  {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
  (hx : s ≫ t = x)

/-- Identify fibre modules using the canonical fibre isomorphism. -/
def fibreModuleIso (F : (pullback c t).Modules) :
    fibreModule c t s F ≅ (Scheme.Modules.pullback (fibreIso c t s x hx).hom).obj
      ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).obj F) :=
  (Scheme.Modules.pullbackCongr (fibreIso_hom_baseChangeSnd c t s x hx).symm).app F ≪≫
    ((Scheme.Modules.pullbackComp (fibreIso c t s x hx).hom
      (baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t))).app F).symm

/-- Identify the unit module under the canonical fibre isomorphism. -/
def fibreUnitIso :
    (𝟙_ (pullback (pullback.snd c t) s).Modules) ≅
      (Scheme.Modules.pullback (fibreIso c t s x hx).hom).obj (𝟙_ (pullback c x).Modules) :=
  (Scheme.Modules.pullbackTensorUnitObjIso (fibreIso c t s x hx).hom).symm

end FibreIso

end AlgebraicGeometry.RelPicard

end

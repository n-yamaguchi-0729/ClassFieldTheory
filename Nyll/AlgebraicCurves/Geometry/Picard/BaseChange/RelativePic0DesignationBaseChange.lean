/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelativePic0DesignationBaseChange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Designation
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase

/-!
Base change of a relative Picard-zero designation and the resulting structure morphism and zero
section.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve

namespace GoodReductionJacobian.RelativePic0Designation

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}

/-- Base change of the designated Picard-zero scheme together with its zero section. -/
abbrev baseChange (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R'] :
    RelativePic0Designation R' (SmoothProperCurve.baseChange R c R') where
  P := pullback D.toBase (specMap R R')
  toBase := pullback.snd D.toBase (specMap R R')
  zeroSection := pullback.lift (specMap R R' ≫ D.zeroSection) (𝟙 _)
    (by rw [Category.assoc, D.zeroSection_toBase, Category.comp_id, Category.id_comp])
  zeroSection_toBase := pullback.lift_snd _ _ _

variable (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']

theorem baseChange_P : (D.baseChange R').P = pullback D.toBase (specMap R R') := rfl

theorem baseChange_toBase : (D.baseChange R').toBase = pullback.snd D.toBase (specMap R R') := rfl

theorem baseChange_zeroSection :
    (D.baseChange R').zeroSection = pullback.lift (specMap R R' ≫ D.zeroSection) (𝟙 _)
      (by rw [Category.assoc, D.zeroSection_toBase, Category.comp_id, Category.id_comp]) := rfl

theorem baseChange_zeroSection_fst :
    (D.baseChange R').zeroSection ≫ pullback.fst D.toBase (specMap R R') = specMap R R' ≫
      D.zeroSection :=
  pullback.lift_fst _ _ _

open NeronModelInfra

/-- Lift the same point to the pullback defining the base-changed designation. -/
def baseChangeLift {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
    (a : SchemeHomOver (t ≫ specMap R R') D.toBase) :
    SchemeHomOver t (D.baseChange R').toBase :=
  ⟨pullback.lift a.1 t a.2, pullback.lift_snd _ _ _⟩

/-- The first projection of the base change lift is the original point. -/
theorem baseChangeLift_fst {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
    (a : SchemeHomOver (t ≫ specMap R R') D.toBase) :
    (baseChangeLift D R' t a).1 ≫ pullback.fst D.toBase (specMap R R') = a.1 :=
  pullback.lift_fst _ _ _

/-- The first projection determines a point of the base-changed designation. -/
theorem eq_baseChangeLift {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
    (z : SchemeHomOver t (D.baseChange R').toBase)
    (a : SchemeHomOver (t ≫ specMap R R') D.toBase)
    (hz : z.1 ≫ pullback.fst D.toBase (specMap R R') = a.1) : z = baseChangeLift D R' t a := by
  apply Subtype.ext
  apply pullback.hom_ext
  · exact hz.trans (baseChangeLift_fst D R' t a).symm
  · exact z.2.trans (pullback.lift_snd _ _ _).symm

end GoodReductionJacobian.RelativePic0Designation

end

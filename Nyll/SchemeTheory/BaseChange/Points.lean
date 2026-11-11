/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GoodReductionJacobian_RelativeGroupLawBaseChange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Nyll.SchemeTheory.BaseChange.SchemeHomOver
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Points of an actual base change

These existing point equivalences require no group law. Their implementation
and declaration names are moved unchanged from the relative-group-law owner.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
variable (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

/-- The scheme obtained by base change along the given morphism. -/
abbrev baseChangeScheme (f : A ⟶ Spec (CommRingCat.of R)) : Scheme.{u} :=
  pullback f ι

/-- The structure morphism of the base-changed scheme. -/
abbrev baseChangeStr (f : A ⟶ Spec (CommRingCat.of R)) :
    baseChangeScheme ι f ⟶ Spec (CommRingCat.of R') :=
  pullback.snd f ι

/-- A point of the base change viewed as a point of the original scheme. -/
def baseChangePointToBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (x : SchemeHomOver t' (baseChangeStr ι f)) : SchemeHomOver (t' ≫ ι) f :=
  ⟨x.1 ≫ pullback.fst f ι, by rw [Category.assoc, pullback.condition, ← Category.assoc, x.2]⟩

/-- A compatible point lifted to the base change by the pullback property. -/
def baseChangePointOfBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (y : SchemeHomOver (t' ≫ ι) f) : SchemeHomOver t' (baseChangeStr ι f) :=
  ⟨pullback.lift y.1 t' y.2, pullback.lift_snd _ _ _⟩
@[simp]
theorem baseChangePointToBase_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (x : SchemeHomOver t' (baseChangeStr ι f)) :
    (baseChangePointToBase ι x).1 = x.1 ≫ pullback.fst f ι :=
  rfl
@[simp]
theorem baseChangePointOfBase_coe {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (y : SchemeHomOver (t' ≫ ι) f) :
    (baseChangePointOfBase ι y).1 = pullback.lift y.1 t' y.2 :=
  rfl
@[simp]
theorem baseChangePointToBase_ofBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (y : SchemeHomOver (t' ≫ ι) f) :
    baseChangePointToBase ι (baseChangePointOfBase ι y) = y :=
  Subtype.ext (pullback.lift_fst _ _ _)
@[simp]
theorem baseChangePointOfBase_toBase {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (x : SchemeHomOver t' (baseChangeStr ι f)) :
    baseChangePointOfBase ι (baseChangePointToBase ι x) = x := by
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [baseChangePointOfBase_coe, pullback.lift_fst, baseChangePointToBase_coe]
  · rw [baseChangePointOfBase_coe, pullback.lift_snd]
    exact x.2.symm

/-- The equivalence between points of the base change and compatible original points. -/
def baseChangePointEquiv {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    SchemeHomOver t' (baseChangeStr ι f) ≃ SchemeHomOver (t' ≫ ι) f where
  toFun := baseChangePointToBase ι
  invFun := baseChangePointOfBase ι
  left_inv := baseChangePointOfBase_toBase ι
  right_inv := baseChangePointToBase_ofBase ι

theorem baseChangePointToBase_schemeHomOverComp {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R')) (t' : T' ⟶ Spec (CommRingCat.of R')) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (x : SchemeHomOver t (baseChangeStr ι f)) :
    baseChangePointToBase ι (schemeHomOverComp ψ hψ x) =
      schemeHomOverComp ψ (by rw [← Category.assoc, hψ]) (baseChangePointToBase ι x) :=
  Subtype.ext (Category.assoc _ _ _)

theorem baseChangePointToBase_comp_fibreRestrictAlong {B : Scheme.{u}}
    {g : B ⟶ Spec (CommRingCat.of R)} (φ : SchemeHomOver g f)
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')} (x : SchemeHomOver t' (baseChangeStr ι g))
      :
    baseChangePointToBase ι (NeronModelInfra.schemeHomOverComp x (fibreRestrictAlong ι f g φ)) =
      NeronModelInfra.schemeHomOverComp (baseChangePointToBase ι x) φ := by
  apply Subtype.ext
  simp only [baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc,
    fibreRestrictAlong_coe_comp_fst]

end GoodReductionJacobian.RelativeGroupLaw

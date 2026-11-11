/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelativeGroupLaw.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
Group laws on test-scheme points over an affine base and their naturality.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory NeronModelInfra

open scoped CategoryTheory.MonObj

namespace GoodReductionJacobian

/-- A group law on relative points, with multiplication natural in the test scheme. -/
structure RelativeGroupLaw (R : Type u) [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) where
  /-- Multiplication of relative points over a test scheme. -/
  mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
    SchemeHomOver t f → SchemeHomOver t f → SchemeHomOver t f
  /-- The identity relative point over each test scheme. -/
  one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), SchemeHomOver t f
  /-- Inversion of relative points over a test scheme. -/
  inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
    SchemeHomOver t f → SchemeHomOver t f
  /-- Multiplication of relative points is associative. -/
  mul_assoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y z : SchemeHomOver t f), mul t (mul t x y) z = mul t x (mul t y z)
  /-- The identity point is a left identity. -/
  one_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
    mul t (one t) x = x
  /-- The identity point is a right identity. -/
  mul_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
    mul t x (one t) = x
  /-- A point multiplied on the left by its inverse gives the identity. -/
  inv_mul_cancel : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f), mul t (inv t x) x = one t
  /-- Multiplication commutes with pullback along morphisms of test schemes. -/
  mul_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x y : SchemeHomOver t f),
    schemeHomOverComp ψ hψ (mul t x y) =
      mul t' (schemeHomOverComp ψ hψ x) (schemeHomOverComp ψ hψ y)

namespace RelativeGroupLaw

/-- The multiplication is commutative on every test-scheme point group. -/
def IsCommutative {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
    G.mul t x y = G.mul t y x

theorem IsCommutative.mul_comm {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} {G : RelativeGroupLaw R f} (hc : G.IsCommutative)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    G.mul t x y = G.mul t y x :=
  hc t x y
/-- The group structure on relative points supplied by the given group law. -/
@[reducible]
def pointGroup {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Group (SchemeHomOver t f) where
  mul x y := G.mul t x y
  one := G.one t
  inv x := G.inv t x
  mul_assoc := G.mul_assoc t
  one_mul := G.one_mul t
  mul_one := G.mul_one t
  inv_mul_cancel := G.inv_mul_cancel t

theorem mul_inv_cancel {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.mul t x (G.inv t x) = G.one t := by
  calc G.mul t x (G.inv t x)
      = G.mul t (G.one t) (G.mul t x (G.inv t x)) := (G.one_mul t _).symm
    _ = G.mul t (G.mul t (G.inv t (G.inv t x)) (G.inv t x)) (G.mul t x (G.inv t x)) := by
        rw [G.inv_mul_cancel t (G.inv t x)]
    _ = G.mul t (G.inv t (G.inv t x)) (G.mul t (G.inv t x) (G.mul t x (G.inv t x))) := by
        rw [G.mul_assoc]
    _ = G.mul t (G.inv t (G.inv t x)) (G.mul t (G.mul t (G.inv t x) x) (G.inv t x)) := by
        rw [G.mul_assoc]
    _ = G.mul t (G.inv t (G.inv t x)) (G.mul t (G.one t) (G.inv t x)) := by
        rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t (G.inv t x)) (G.inv t x) := by rw [G.one_mul]
    _ = G.one t := G.inv_mul_cancel t (G.inv t x)

theorem one_natural {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    schemeHomOverComp ψ hψ (G.one t) = G.one t' := by
  have h : G.mul t' (schemeHomOverComp ψ hψ (G.one t)) (schemeHomOverComp ψ hψ (G.one t)) =
      schemeHomOverComp ψ hψ (G.one t) := by
    rw [← G.mul_natural t t' ψ hψ, G.one_mul]
  calc schemeHomOverComp ψ hψ (G.one t)
      = G.mul t' (G.one t') (schemeHomOverComp ψ hψ (G.one t)) := (G.one_mul t' _).symm
    _ = G.mul t' (G.mul t' (G.inv t' (schemeHomOverComp ψ hψ (G.one t)))
          (schemeHomOverComp ψ hψ (G.one t))) (schemeHomOverComp ψ hψ (G.one t)) := by
        rw [G.inv_mul_cancel]
    _ = G.mul t' (G.inv t' (schemeHomOverComp ψ hψ (G.one t)))
          (G.mul t' (schemeHomOverComp ψ hψ (G.one t)) (schemeHomOverComp ψ hψ (G.one t))) := by
        rw [G.mul_assoc]
    _ = G.mul t' (G.inv t' (schemeHomOverComp ψ hψ (G.one t)))
          (schemeHomOverComp ψ hψ (G.one t)) := by rw [h]
    _ = G.one t' := G.inv_mul_cancel t' _

/-- Multiplication of actual relative points commutes with base equality transport. -/
theorem mul_castBase {R : Type u} [CommRing R] {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {s s' : T ⟶ Spec (CommRingCat.of R)} (e : s = s')
    (a b : SchemeHomOver s f) :
    G.mul s' (SchemeHomOver.castBase e a) (SchemeHomOver.castBase e b) =
      SchemeHomOver.castBase e (G.mul s a b) := by
  subst e; rfl

/-- The actual identity point commutes with base equality transport. -/
theorem one_castBase {R : Type u} [CommRing R] {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {s s' : T ⟶ Spec (CommRingCat.of R)} (e : s = s') :
    SchemeHomOver.castBase e (G.one s) = G.one s' := by
  subst e; rfl

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_polynomial_eval_eq_endDegree_zpow_mul_of_abelianSchemePropertyBundle.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

section PointEvaluation

variable {R : Type u} [CommRing R] {A : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)

local infixl:80 " ⊚ " => NeronModelInfra.schemeHomOverComp

/-- Evaluating relative self-morphisms at a point preserves multiplication. -/
theorem pointEval_mul {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (z : SchemeHomOver t f)
    (β δ : SchemeHomOver f f) :
    z ⊚ (L.mul f β δ) = L.mul t (z ⊚ β) (z ⊚ δ) := by
  have h := L.mul_natural f t z.1 z.2 β δ
  have e : ∀ δ : SchemeHomOver f f, GoodReductionJacobian.schemeHomOverComp z.1 z.2 δ = z ⊚ δ :=
    fun δ => Subtype.ext rfl
  rw [e, e, e] at h
  exact h

/-- Evaluating relative self-morphisms at a point preserves the identity. -/
theorem pointEval_one {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (z : SchemeHomOver t f) :
    z ⊚ (L.one f) = L.one t := by
  have h := L.one_natural f t z.1 z.2
  have e : GoodReductionJacobian.schemeHomOverComp z.1 z.2 (L.one f) = z ⊚ (L.one f) := Subtype.ext
    rfl
  rw [e] at h
  exact h

/-- Evaluation at an actual point, using the two point groups of the given law. -/
def pointEvalHom {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (z : SchemeHomOver t f) :
    let _ : Group (SchemeHomOver f f) := L.pointGroup f
    let _ : Group (SchemeHomOver t f) := L.pointGroup t
    SchemeHomOver f f →* SchemeHomOver t f := by
  intro sourceGroup targetGroup
  exact
    { toFun := fun δ => z ⊚ δ
      map_one' := pointEval_one L z
      map_mul' := fun β δ => pointEval_mul L z β δ }

end PointEvaluation

end RelativeGroupLaw

/-- The unique pointwise group law on the identity morphism of the base spectrum. -/
def trivialRelativeGroupLaw (R : Type u) [CommRing R] :
    RelativeGroupLaw R (𝟙 (Spec (CommRingCat.of R))) where
  mul := fun _ x _ => x
  one := fun t => ⟨t, Category.comp_id t⟩
  inv := fun _ x => x
  mul_assoc := fun _ _ _ _ => rfl
  one_mul := fun t _ =>
    (subsingleton_schemeHomOver_of_isIso t (𝟙 (Spec (CommRingCat.of R)))).allEq _ _
  mul_one := fun _ _ => rfl
  inv_mul_cancel := fun t _ =>
    (subsingleton_schemeHomOver_of_isIso t (𝟙 (Spec (CommRingCat.of R)))).allEq _ _
  mul_natural := fun _ _ _ _ _ _ => rfl

theorem relativeGroupLaw_pointwise_eq_of_isIso {R : Type u} [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) [IsIso f]
    (G G' : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t f) :
    G.mul t x y = G'.mul t x y ∧ G.one t = G'.one t ∧ G.inv t x = G'.inv t x :=
  ⟨(subsingleton_schemeHomOver_of_isIso t f).allEq _ _,
    (subsingleton_schemeHomOver_of_isIso t f).allEq _ _,
    (subsingleton_schemeHomOver_of_isIso t f).allEq _ _⟩

end GoodReductionJacobian

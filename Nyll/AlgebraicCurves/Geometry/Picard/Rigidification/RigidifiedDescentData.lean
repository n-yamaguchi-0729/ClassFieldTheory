/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_descent_finite_faithfullyFlat_of_bijective_sections.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Nyll.AlgebraicCurves.Geometry.Picard.BaseChange.IsPullbackBaseChangeSnd
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
public import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.RigidifiedBundleIsoMapPullbackRigSectionCompEq
public import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.RigidifiedBundleSubsingletonIsoMapPullbackRigSectionCompEq
public import Nyll.SchemeTheory.Modules.Functoriality.PullbackCompPullbackCongrPasteSquaresApp

/-! # Actual overlap data for rigidified descent

These constructions share the original pairwise and triple pullback maps, the
rigidifications selected from the supplied line bundles, and the isomorphisms
chosen from the same rigidification compatibility statement. The index universe
is independent of the scheme universe. Effective descent for an open cover or a
flat affine morphism remains in the corresponding consuming module.
-/

@[expose] public section

noncomputable section

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open NeronModelInfra AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.RelPicard.RigidifiedDescent

section Coherence
variable {X₀ X₁ X₂ X₃ : Scheme.{u}}

theorem pullbackComp_paste (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) :
    Functor.whiskerLeft (Scheme.Modules.pullback h) (Scheme.Modules.pullbackComp f g).hom ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).hom =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Scheme.Modules.pullbackComp g h).hom (Scheme.Modules.pullback f) ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).hom ≫ eqToHom (by rw [Category.assoc]) := by
  have H0 := Scheme.Modules.pseudofunctor_associativity f g h
  have H1 : Functor.whiskerLeft (Scheme.Modules.pullback h) (Scheme.Modules.pullbackComp f g).hom ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).hom =
      (Functor.associator _ _ _).inv ≫
        (Functor.isoWhiskerRight (Scheme.Modules.pullbackComp g h)
          (Scheme.Modules.pullback f)).hom ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).hom ≫
        ((Scheme.Modules.pullbackComp f (g ≫ h)).inv ≫
          Functor.whiskerRight (Scheme.Modules.pullbackComp g h).inv (Scheme.Modules.pullback f) ≫
          (Functor.associator _ _ _).hom ≫
            Functor.whiskerLeft (Scheme.Modules.pullback h) (Scheme.Modules.pullbackComp f g).hom ≫
            (Scheme.Modules.pullbackComp (f ≫ g) h).hom) := by
    rw [Iso.hom_inv_id_assoc, Functor.isoWhiskerRight_hom, ← Functor.whiskerRight_comp_assoc,
      Iso.hom_inv_id,
      Functor.whiskerRight_id', Category.id_comp, Iso.inv_hom_id_assoc]
  rw [H0] at H1
  exact H1

theorem pullbackComp_paste_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (M : X₃.Modules) :
    (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
          (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫
        eqToHom (by rw [Category.assoc]) := by
  have H := NatTrans.congr_app (pullbackComp_paste f g h) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app,
    Category.id_comp, eqToHom_app] at H
  exact H

/-- The pullback comparison for a specified equality between a composite and a map. -/
def τ (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m)
    : Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f ≅ Scheme.Modules.pullback m :=
  Scheme.Modules.pullbackComp f g ≪≫ Scheme.Modules.pullbackCongr e

theorem τ_hom_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) (M : X₂.Modules) :
    (τ f g m e).hom.app M = (Scheme.Modules.pullbackComp f g).hom.app M ≫ eqToHom (by rw [e]) := by
  subst e
  rfl

theorem τ_inv_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) (M : X₂.Modules) :
    (τ f g m e).inv.app M = eqToHom (by rw [e]) ≫ (Scheme.Modules.pullbackComp f g).inv.app M := by
  subst e
  rfl

theorem τ_paste_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)
    (fg : X₀ ⟶ X₂) (gh : X₁ ⟶ X₃) (m : X₀ ⟶ X₃)
    (e₁ : f ≫ g = fg) (e₂ : g ≫ h = gh) (e₃ : fg ≫ h = m) (M : X₃.Modules) :
    (τ f g fg e₁).hom.app ((Scheme.Modules.pullback h).obj M) ≫ (τ fg h m e₃).hom.app M =
      (Scheme.Modules.pullback f).map ((τ g h gh e₂).hom.app M) ≫
          (τ f gh m (by rw [← e₂, ← Category.assoc, e₁, e₃])).hom.app M := by
  subst e₁ e₂ e₃
  simp only [τ_hom_app, eqToHom_refl, Category.comp_id]
  rw [pullbackComp_paste_app]

/-- The natural isomorphism between pullback functors around a commutative square. -/
def sqIso {W X Y Z : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Z} {h : W ⟶ Y} {k : Y ⟶ Z}
    (e : f ≫ g = h ≫ k)
    : Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f ≅
      Scheme.Modules.pullback k ⋙ Scheme.Modules.pullback h :=
  Scheme.Modules.pullbackComp f g ≪≫ Scheme.Modules.pullbackCongr e ≪≫
    (Scheme.Modules.pullbackComp h k).symm

theorem route {X X₀' X₁' Y Y₀ Y₁ : Scheme.{u}}
    (a : X₀' ⟶ X₁') (b : X₁' ⟶ X) (d : X₀' ⟶ X) (e : a ≫ b = d)
    (s₀ : Y₀ ⟶ X₀') (s₁ : Y₁ ⟶ X₁') (s : Y ⟶ X)
    (r : Y₀ ⟶ Y₁) (p : Y₁ ⟶ Y) (m : Y₀ ⟶ Y) (G : r ≫ p = m)
    (E : s₀ ≫ a = r ≫ s₁) (F : s₁ ≫ b = p ≫ s) (H : s₀ ≫ d = m ≫ s) (M : X.Modules) :
    (sqIso E).hom.app ((Scheme.Modules.pullback b).obj M) ≫
        (Scheme.Modules.pullback r).map ((sqIso F).hom.app M) ≫
        (τ r p m G).hom.app ((Scheme.Modules.pullback s).obj M) =
      (Scheme.Modules.pullback s₀).map ((τ a b d e).hom.app M) ≫ (sqIso H).hom.app M :=
  AlgebraicGeometry.Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app
    a b d e s₀ s₁ s r p m G E F H M

end Coherence

/-- Pull back a line-bundle isomorphism and identify the composite pullbacks with chosen maps. -/
def pullHomIso {X₁ X₂ Y Y' : Scheme.{u}} {M₁ : X₁.Modules} {M₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (Φ : (Scheme.Modules.pullback f₁).obj M₁ ≅ (Scheme.Modules.pullback f₂).obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (Scheme.Modules.pullback gf₁).obj M₁ ≅ (Scheme.Modules.pullback gf₂).obj M₂ :=
  ((τ g f₁ gf₁ hgf₁).app M₁).symm ≪≫ (Scheme.Modules.pullback g).mapIso Φ ≪≫
    (τ g f₂ gf₂ hgf₂).app M₂

theorem pullHomIso_hom' {X₁ X₂ Y Y' : Scheme.{u}} {M₁ : X₁.Modules} {M₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (Φ : (Scheme.Modules.pullback f₁).obj M₁ ≅ (Scheme.Modules.pullback f₂).obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (pullHomIso Φ g gf₁ gf₂ hgf₁ hgf₂).hom =
      (τ g f₁ gf₁ hgf₁).inv.app M₁ ≫ (Scheme.Modules.pullback g).map Φ.hom ≫
          (τ g f₂ gf₂ hgf₂).hom.app M₂ :=
  rfl

section Overlaps

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))

lemma isPullback_baseChangeSnd_snd {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    IsPullback (baseChangeSnd c ψ) (pullback.snd c t') (pullback.snd c t) ψ.1 :=
  _root_.AlgebraicGeometry.RelPicard.isPullback_baseChangeSnd c ψ

lemma isPullback_baseChangeSnd {X U V W : Scheme.{u}} {x : X ⟶ Spec (CommRingCat.of R)}
    {uS : U ⟶ Spec (CommRingCat.of R)} {vS : V ⟶ Spec (CommRingCat.of R)}
    {wS : W ⟶ Spec (CommRingCat.of R)}
    (u : SchemeHomOver uS x) (v : SchemeHomOver vS x)
    (a : SchemeHomOver wS uS) (b : SchemeHomOver wS vS)
    (h : IsPullback a.1 b.1 u.1 v.1) :
    IsPullback (baseChangeSnd c a) (baseChangeSnd c b) (baseChangeSnd c u) (baseChangeSnd c v) :=
  _root_.AlgebraicGeometry.RelPicard.isPullback_baseChangeSnd_of_isPullback c u v a b h

/-- The structure map of the overlap of two schemes over the same base. -/
abbrev strMap₁₂ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    Limits.pullback ψ₁.1 ψ₂.1 ⟶ Spec (CommRingCat.of R) :=
  pullback.fst ψ₁.1 ψ₂.1 ≫ t₁

/-- The first overlap projection as a morphism over the base. -/
def pr₁ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    SchemeHomOver (strMap₁₂ ψ₁ ψ₂) t₁ :=
  ⟨pullback.fst ψ₁.1 ψ₂.1, rfl⟩

/-- The second overlap projection as a morphism over the base. -/
def pr₂ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    SchemeHomOver (strMap₁₂ ψ₁ ψ₂) t₂ :=
  ⟨pullback.snd ψ₁.1 ψ₂.1, by
    have h2 : pullback.snd ψ₁.1 ψ₂.1 ≫ ψ₂.1 ≫ t = pullback.snd ψ₁.1 ψ₂.1 ≫ t₂ := by rw [ψ₂.2]
    have h1 : pullback.fst ψ₁.1 ψ₂.1 ≫ ψ₁.1 ≫ t = pullback.fst ψ₁.1 ψ₂.1 ≫ t₁ := by rw [ψ₁.2]
    change pullback.snd ψ₁.1 ψ₂.1 ≫ t₂ = pullback.fst ψ₁.1 ψ₂.1 ≫ t₁
    rw [← h2, ← h1, ← Category.assoc, ← pullback.condition, Category.assoc]⟩

@[scoped simp] lemma pr₁_val {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    (pr₁ ψ₁ ψ₂).1 = pullback.fst ψ₁.1 ψ₂.1 := rfl

@[scoped simp] lemma pr₂_val {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)}
    {t₂ : T₂ ⟶ Spec (CommRingCat.of R)} (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    (pr₂ ψ₁ ψ₂).1 = pullback.snd ψ₁.1 ψ₂.1 := rfl

lemma postComp_pr₁_eq_postComp_pr₂ {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    postComp ψ₁ (pr₁ ψ₁ ψ₂) = postComp ψ₂ (pr₂ ψ₁ ψ₂) :=
  Subtype.ext pullback.condition

/-- The chosen pullback square for the two induced base-change morphisms. -/
def chosenPullback {T T₁ T₂ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) :
    ChosenPullback (baseChangeSnd c ψ₁) (baseChangeSnd c ψ₂) where
  pullback := Limits.pullback c (strMap₁₂ ψ₁ ψ₂)
  p₁ := baseChangeSnd c (pr₁ ψ₁ ψ₂)
  p₂ := baseChangeSnd c (pr₂ ψ₁ ψ₂)
  condition := by
    rw [baseChangeSnd_comp, baseChangeSnd_comp, postComp_pr₁_eq_postComp_pr₂]
  isLimit := (isPullback_baseChangeSnd c ψ₁ ψ₂ (pr₁ ψ₁ ψ₂) (pr₂ ψ₁ ψ₂)
    (IsPullback.of_hasPullback ψ₁.1 ψ₂.1)).isLimit
  p := baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₂))
  hp₁ := baseChangeSnd_comp c _ _

section three
variable {T T₁ T₂ T₃ : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t₁ : T₁ ⟶ Spec (CommRingCat.of R)} {t₂ : T₂ ⟶ Spec (CommRingCat.of R)}
    {t₃ : T₃ ⟶ Spec (CommRingCat.of R)}
    (ψ₁ : SchemeHomOver t₁ t) (ψ₂ : SchemeHomOver t₂ t) (ψ₃ : SchemeHomOver t₃ t)

/-- The projection from the triple overlap to the first two factors. -/
abbrev ρ₁₂ : SchemeHomOver (strMap₁₂ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)) (strMap₁₂ ψ₁ ψ₂)
    := pr₁ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)

/-- The projection from the triple overlap to the last two factors. -/
abbrev ρ₂₃ : SchemeHomOver (strMap₁₂ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)) (strMap₁₂ ψ₂ ψ₃)
    := pr₂ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)

/-- The projection from the triple overlap to the first and third factors. -/
def ρ₁₃ : SchemeHomOver (strMap₁₂ (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)) (strMap₁₂ ψ₁ ψ₃) :=
  ⟨pullback.lift ((ρ₁₂ ψ₁ ψ₂ ψ₃).1 ≫ (pr₁ ψ₁ ψ₂).1) ((ρ₂₃ ψ₁ ψ₂ ψ₃).1 ≫ (pr₂ ψ₂ ψ₃).1)
      (by
        have hT₂ : pullback.fst ψ₁.1 ψ₂.1 ≫ ψ₁.1 = pullback.snd ψ₁.1 ψ₂.1 ≫ ψ₂.1
          := pullback.condition
        have hT₂' : pullback.fst ψ₂.1 ψ₃.1 ≫ ψ₂.1 = pullback.snd ψ₂.1 ψ₃.1 ≫ ψ₃.1
          := pullback.condition
        have hT₃ : pullback.fst (pullback.snd ψ₁.1 ψ₂.1) (pullback.fst ψ₂.1 ψ₃.1)
            ≫ pullback.snd ψ₁.1 ψ₂.1 =
            pullback.snd (pullback.snd ψ₁.1 ψ₂.1) (pullback.fst ψ₂.1 ψ₃.1)
              ≫ pullback.fst ψ₂.1 ψ₃.1 :=
          pullback.condition
        simp only [pr₁_val, pr₂_val, Category.assoc]
        rw [hT₂, ← Category.assoc, hT₃, Category.assoc, hT₂']),
    by
      simp only [pr₁_val, pr₂_val]
      rw [← Category.assoc, pullback.lift_fst, Category.assoc]
      rfl⟩

lemma ρ₁₃_pr₁ : postComp (pr₁ ψ₁ ψ₃) (ρ₁₃ ψ₁ ψ₂ ψ₃) = postComp (pr₁ ψ₁ ψ₂) (ρ₁₂ ψ₁ ψ₂ ψ₃) :=
  Subtype.ext (pullback.lift_fst _ _ _)

lemma ρ₁₃_pr₂ : postComp (pr₂ ψ₁ ψ₃) (ρ₁₃ ψ₁ ψ₂ ψ₃) = postComp (pr₂ ψ₂ ψ₃) (ρ₂₃ ψ₁ ψ₂ ψ₃) :=
  Subtype.ext (pullback.lift_snd _ _ _)

lemma ρ₂₃_pr₁ : postComp (pr₁ ψ₂ ψ₃) (ρ₂₃ ψ₁ ψ₂ ψ₃) = postComp (pr₂ ψ₁ ψ₂) (ρ₁₂ ψ₁ ψ₂ ψ₃) :=
  Subtype.ext pullback.condition.symm

/-- The compatible threefold pullback data for the induced base-change morphisms. -/
def chosenPullback₃ :
    ChosenPullback₃ (chosenPullback c ψ₁ ψ₂) (chosenPullback c ψ₂ ψ₃) (chosenPullback c ψ₁ ψ₃) where
  chosenPullback := chosenPullback c (pr₂ ψ₁ ψ₂) (pr₁ ψ₂ ψ₃)
  p := baseChangeSnd c (postComp (postComp ψ₁ (pr₁ ψ₁ ψ₂)) (ρ₁₂ ψ₁ ψ₂ ψ₃))
  p₁ := baseChangeSnd c (postComp (pr₁ ψ₁ ψ₂) (ρ₁₂ ψ₁ ψ₂ ψ₃))
  p₃ := baseChangeSnd c (postComp (pr₂ ψ₂ ψ₃) (ρ₂₃ ψ₁ ψ₂ ψ₃))
  l :=
    { f := baseChangeSnd c (ρ₁₃ ψ₁ ψ₂ ψ₃)
      f_p₁ := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (pr₁ ψ₁ ψ₃) = _
        rw [baseChangeSnd_comp, ρ₁₃_pr₁]
      f_p₂ := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (pr₂ ψ₁ ψ₃) = _
        rw [baseChangeSnd_comp, ρ₁₃_pr₂]
      f_p := by
        change baseChangeSnd c _ ≫ baseChangeSnd c (postComp ψ₁ (pr₁ ψ₁ ψ₃)) = _
        rw [baseChangeSnd_comp]
        congr 1
        exact Subtype.ext (by
          change (ρ₁₃ ψ₁ ψ₂ ψ₃).1 ≫ (pr₁ ψ₁ ψ₃).1 ≫ ψ₁.1 = (ρ₁₂ ψ₁ ψ₂ ψ₃).1 ≫ (pr₁ ψ₁ ψ₂).1 ≫ ψ₁.1
          simp only [← Category.assoc]
          congr 1
          exact pullback.lift_fst _ _ _) }
  hp₁ := by
    change baseChangeSnd c (ρ₁₂ ψ₁ ψ₂ ψ₃) ≫ baseChangeSnd c (pr₁ ψ₁ ψ₂) = _
    rw [baseChangeSnd_comp]
  hp₃ := by
    change baseChangeSnd c (ρ₂₃ ψ₁ ψ₂ ψ₃) ≫ baseChangeSnd c (pr₂ ψ₂ ψ₃) = _
    rw [baseChangeSnd_comp]

end three

end Overlaps

section Rigidification

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

section Theta
variable {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
  {ι : Type w} {U : ι → Scheme.{u}} {u : ∀ i, U i ⟶ Spec (CommRingCat.of R)}
  (f : ∀ i, SchemeHomOver (u i) t) (M : ∀ i, RigidifiedLineBundle c ε (u i))

/-- The unit module sheaf on the base scheme. -/
abbrev EE (T : Scheme.{u}) : T.Modules := SheafOfModules.unit T.ringCatSheaf

/-- The local rigidification, identified with the pullback of the unit module on the base. -/
def β (i : ι) :
    (Scheme.Modules.pullback (rigSection c (u i) ε)).obj (M i).L
        ≅ (Scheme.Modules.pullback (f i).1).obj (EE T) :=
  (M i).rigidified.some ≪≫ (Scheme.Modules.pullbackUnitIso (f i).1).symm

/-- Transport a local rigidification through the given commuting square and base morphism. -/
def Θ (i : ι) {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    (g₁ : Limits.pullback c z ⟶ Limits.pullback c (u i)) (ζ₁ : Z ⟶ U i)
    (S₁ : rigSection c z ε ≫ g₁ = ζ₁ ≫ rigSection c (u i) ε) (ζT : Z ⟶ T) (h₁ : ζ₁ ≫ (f i).1 = ζT) :
    (Scheme.Modules.pullback (rigSection c z ε)).obj
        ((Scheme.Modules.pullback g₁).obj (M i).L)
        ≅ (Scheme.Modules.pullback ζT).obj (EE T) :=
  (sqIso S₁).app (M i).L ≪≫ (Scheme.Modules.pullback ζ₁).mapIso (β c ε f M i) ≪≫
    (τ ζ₁ (f i).1 ζT h₁).app (EE T)

end Theta

section Rigidity
variable {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))

theorem iso_eq_of_map_rigSection_eq
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      let : Algebra A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤) :=
        Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    {L₁ L₂ : (Limits.pullback c z).Modules}
    (h₁ : Scheme.Modules.IsInvertible L₁) (h₂ : Scheme.Modules.IsInvertible L₂)
    (r₂ : Nonempty ((Scheme.Modules.pullback (rigSection c z ε)).obj L₂
        ≅ SheafOfModules.unit Z.ringCatSheaf))
    (φ ψ : L₁ ≅ L₂)
    (h : (Scheme.Modules.pullback (rigSection c z ε)).map φ.hom
        = (Scheme.Modules.pullback (rigSection c z ε)).map ψ.hom) :
    φ = ψ := by
  let α' := r₂.some
  let α := (Scheme.Modules.pullback (rigSection c z ε)).mapIso φ ≪≫ α'
  let M₁ : RigidifiedLineBundle c ε z := ⟨L₁, h₁, ⟨α⟩⟩
  let M₂ : RigidifiedLineBundle c ε z := ⟨L₂, h₂, ⟨α'⟩⟩
  have hs := RigidifiedLineBundle.subsingleton_iso_map_pullback_rigSection_comp_eq
    R c ε hH0 z M₁ M₂ α α'
  have hφ : (Scheme.Modules.pullback (rigSection c z ε)).mapIso φ ≪≫ α' = α := rfl
  have hψ : (Scheme.Modules.pullback (rigSection c z ε)).mapIso ψ ≪≫ α' = α := by
    have e : (Scheme.Modules.pullback (rigSection c z ε)).mapIso ψ
        = (Scheme.Modules.pullback (rigSection c z ε)).mapIso φ :=
      Iso.ext h.symm
    rw [e]
  exact congrArg Subtype.val (hs.elim ⟨φ, hφ⟩ ⟨ψ, hψ⟩)

theorem hom_eq_of_map_rigSection_eq
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      let : Algebra A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤) :=
        Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    {L₁ L₂ : (Limits.pullback c z).Modules}
    (h₁ : Scheme.Modules.IsInvertible L₁) (h₂ : Scheme.Modules.IsInvertible L₂)
    (r₂ : Nonempty ((Scheme.Modules.pullback (rigSection c z ε)).obj L₂
        ≅ SheafOfModules.unit Z.ringCatSheaf))
    (φ ψ : L₁ ⟶ L₂) (hφ : IsIso φ) (hψ : IsIso ψ)
    (h : (Scheme.Modules.pullback (rigSection c z ε)).map φ
        = (Scheme.Modules.pullback (rigSection c z ε)).map ψ) :
    φ = ψ :=
  congrArg Iso.hom (iso_eq_of_map_rigSection_eq c ε z hH0 h₁ h₂ r₂ (asIso φ) (asIso ψ) h)

theorem exists_iso_map_rigSection_eq {L₁ L₂ : (Limits.pullback c z).Modules}
    (h₁ : Scheme.Modules.IsInvertible L₁) (h₂ : Scheme.Modules.IsInvertible L₂) {W : Z.Modules}
    (θ₁ : (Scheme.Modules.pullback (rigSection c z ε)).obj L₁ ≅ W)
    (θ₂ : (Scheme.Modules.pullback (rigSection c z ε)).obj L₂ ≅ W)
    (ω : W ≅ SheafOfModules.unit Z.ringCatSheaf) (e : Nonempty (L₁ ≅ L₂)) :
    ∃ Φ : L₁ ≅ L₂, (Scheme.Modules.pullback (rigSection c z ε)).map Φ.hom = θ₁.hom ≫ θ₂.inv := by
  let M₁ : RigidifiedLineBundle c ε z := ⟨L₁, h₁, ⟨θ₁ ≪≫ ω⟩⟩
  let M₂ : RigidifiedLineBundle c ε z := ⟨L₂, h₂, ⟨θ₂ ≪≫ ω⟩⟩
  obtain ⟨Φ, hΦ⟩ :=
    AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_iso_map_pullback_rigSection_comp_eq
      R c ε z M₁ M₂ (θ₁ ≪≫ ω) (θ₂ ≪≫ ω) e.some
  refine ⟨Φ, ?_⟩
  have h : (Scheme.Modules.pullback (rigSection c z ε)).map Φ.hom ≫ θ₂.hom ≫ ω.hom =
      θ₁.hom ≫ ω.hom := congrArg Iso.hom hΦ
  exact (Iso.eq_comp_inv (C := Z.Modules) θ₂).2
    ((Iso.cancel_iso_hom_right (C := Z.Modules)
      ((Scheme.Modules.pullback (rigSection c z ε)).map Φ.hom ≫ θ₂.hom)
      θ₁.hom ω).1
      ((Category.assoc (obj := Z.Modules)
        ((Scheme.Modules.pullback (rigSection c z ε)).map Φ.hom) θ₂.hom ω.hom).trans h))

end Rigidity

section Datum
variable {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
  {ι : Type w} {U : ι → Scheme.{u}} {u : ∀ i, U i ⟶ Spec (CommRingCat.of R)}
  (f : ∀ i, SchemeHomOver (u i) t) (M : ∀ i, RigidifiedLineBundle c ε (u i))
  (hM : ∀ (i j : ι) (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
    (p₁ : SchemeHomOver z (u i)) (p₂ : SchemeHomOver z (u j)),
    p₁.1 ≫ (f i).1 = p₂.1 ≫ (f j).1 →
        Nonempty (((M i).pullbackAlong p₁).L ≅ ((M j).pullbackAlong p₂).L))

/-- The base-change morphism from a local curve chart to the curve over the full base. -/
def fF (i : ι) : Limits.pullback c (u i) ⟶ Limits.pullback c t := baseChangeSnd c (f i)

/-- The chosen pullback square of two local curve charts. -/
def sqF (i j : ι) : ChosenPullback (fF c f i) (fF c f j) := chosenPullback c (f i) (f j)

/-- The chosen threefold pullback data for three local curve charts. -/
def sq₃F (i j k : ι) : ChosenPullback₃ (sqF c f i j) (sqF c f j k) (sqF c f i k)
    := chosenPullback₃ c (f i) (f j) (f k)

/-- The map from a pairwise overlap to the base. -/
abbrev wT (i j : ι) : Limits.pullback (f i).1 (f j).1 ⟶ T := (pr₁ (f i) (f j)).1 ≫ (f i).1

lemma pr₂_comp_eq_wT (i j : ι) : (pr₂ (f i) (f j)).1 ≫ (f j).1 = wT f i j := pullback.condition.symm

/-- The rigidification from the first chart transported to a pairwise overlap. -/
abbrev Θ₁ (i j : ι) :=
  Θ c ε f M i (strMap₁₂ (f i) (f j)) (baseChangeSnd c (pr₁ (f i) (f j))) (pr₁ (f i) (f j)).1
    (rigSection_baseChangeSnd c ε _) (wT f i j) rfl

/-- The rigidification from the second chart transported to a pairwise overlap. -/
abbrev Θ₂ (i j : ι) :=
  Θ c ε f M j (strMap₁₂ (f i) (f j)) (baseChangeSnd c (pr₂ (f i) (f j))) (pr₂ (f i) (f j)).1
    (rigSection_baseChangeSnd c ε _) (wT f i j) (pr₂_comp_eq_wT f i j)

include hM in
theorem exists_homIso (i j : ι) :
    ∃ Φ : (Scheme.Modules.pullback (baseChangeSnd c (pr₁ (f i) (f j)))).obj (M i).L ≅
        (Scheme.Modules.pullback (baseChangeSnd c (pr₂ (f i) (f j)))).obj (M j).L,
      (Scheme.Modules.pullback (rigSection c (strMap₁₂ (f i) (f j)) ε)).map Φ.hom =
        (Θ₁ c ε f M i j).hom ≫ (Θ₂ c ε f M i j).inv :=
  exists_iso_map_rigSection_eq c ε _ ((M i).isInvertible.pullback _) ((M j).isInvertible.pullback _)
    (Θ₁ c ε f M i j) (Θ₂ c ε f M i j) (Scheme.Modules.pullbackUnitIso (wT f i j))
    (hM i j _ _ (pr₁ (f i) (f j)) (pr₂ (f i) (f j)) pullback.condition)

include hM in
/-- Choose an isomorphism between the local line bundles on their pairwise overlap. -/
def homIso (i j : ι) :
    (Scheme.Modules.pullback (baseChangeSnd c (pr₁ (f i) (f j)))).obj (M i).L ≅
      (Scheme.Modules.pullback (baseChangeSnd c (pr₂ (f i) (f j)))).obj (M j).L :=
  (exists_homIso c ε f M hM i j).choose

theorem map_homIso (i j : ι) :
    (Scheme.Modules.pullback (rigSection c (strMap₁₂ (f i) (f j)) ε)).map
        (homIso c ε f M hM i j).hom =
      (Θ₁ c ε f M i j).hom ≫ (Θ₂ c ε f M i j).inv :=
  (exists_homIso c ε f M hM i j).choose_spec

section Half
variable (k : ι) {W Z : Scheme.{u}} {w : W ⟶ Spec (CommRingCat.of R)}
    {z : Z ⟶ Spec (CommRingCat.of R)}
    (π : SchemeHomOver w (u k)) (wT' : W ⟶ T) (hw : π.1 ≫ (f k).1 = wT')
    (ζ : SchemeHomOver z w) (g : Limits.pullback c z ⟶ Limits.pullback c (u k))
    (hg : baseChangeSnd c ζ ≫ baseChangeSnd c π = g)
    (ζ₁ : Z ⟶ U k) (hζ₁ : ζ.1 ≫ π.1 = ζ₁) (S₁ : rigSection c z ε ≫ g = ζ₁ ≫ rigSection c (u k) ε)
    (ζT : Z ⟶ T) (h₁ : ζ₁ ≫ (f k).1 = ζT) (hT : ζ.1 ≫ wT' = ζT)

include hg hζ₁ S₁ in
theorem half_A :
    (Scheme.Modules.pullback (rigSection c z ε)).map
        ((τ (baseChangeSnd c ζ) (baseChangeSnd c π) g hg).inv.app (M k).L) ≫
      (sqIso (rigSection_baseChangeSnd c ε ζ)).hom.app
          ((Scheme.Modules.pullback (baseChangeSnd c π)).obj (M k).L) ≫
      (Scheme.Modules.pullback ζ.1).map ((sqIso (rigSection_baseChangeSnd c ε π)).hom.app (M k).L) =
    (sqIso S₁).hom.app (M k).L ≫
      (τ ζ.1 π.1 ζ₁ hζ₁).inv.app ((Scheme.Modules.pullback (rigSection c (u k) ε)).obj (M k).L) :=
  (Iso.inv_comp_eq ((Scheme.Modules.pullback (rigSection c z ε)).mapIso
      ((τ (baseChangeSnd c ζ) (baseChangeSnd c π) g hg).app (M k).L))).mpr
    (((Iso.eq_comp_inv ((τ ζ.1 π.1 ζ₁ hζ₁).app
          ((Scheme.Modules.pullback (rigSection c (u k) ε)).obj (M k).L))).mpr
      ((Category.assoc _ _ _).trans
        (route (baseChangeSnd c ζ) (baseChangeSnd c π) g hg (rigSection c z ε) (rigSection c w ε)
          (rigSection c (u k) ε) ζ.1 π.1 ζ₁ hζ₁ (rigSection_baseChangeSnd c ε ζ)
            (rigSection_baseChangeSnd c ε π)
          S₁ (M k).L))).trans (Category.assoc _ _ _))

include hζ₁ in
theorem half_B :
    (τ ζ.1 π.1 ζ₁ hζ₁).inv.app ((Scheme.Modules.pullback (rigSection c (u k) ε)).obj (M k).L) ≫
      (Scheme.Modules.pullback ζ.1).map ((Scheme.Modules.pullback π.1).map (β c ε f M k).hom) =
    (Scheme.Modules.pullback ζ₁).map (β c ε f M k).hom ≫
      (τ ζ.1 π.1 ζ₁ hζ₁).inv.app ((Scheme.Modules.pullback (f k).1).obj (EE T)) :=
  ((τ ζ.1 π.1 ζ₁ hζ₁).inv.naturality (β c ε f M k).hom).symm

include hζ₁ hw h₁ hT in
theorem half_C :
    (τ ζ.1 π.1 ζ₁ hζ₁).inv.app ((Scheme.Modules.pullback (f k).1).obj (EE T)) ≫
      (Scheme.Modules.pullback ζ.1).map ((τ π.1 (f k).1 wT' hw).hom.app (EE T)) =
    (τ ζ₁ (f k).1 ζT h₁).hom.app (EE T) ≫ (τ ζ.1 wT' ζT hT).inv.app (EE T) :=
  (Iso.inv_comp_eq ((τ ζ.1 π.1 ζ₁ hζ₁).app ((Scheme.Modules.pullback (f k).1).obj (EE T)))).mpr
    (((Iso.eq_comp_inv ((τ ζ.1 wT' ζT hT).app (EE T))).mpr
      (τ_paste_app ζ.1 π.1 (f k).1 ζ₁ wT' ζT hζ₁ hw h₁ (EE T)).symm).trans (Category.assoc _ _ _))

include hζ₁ in
theorem half :
    (Scheme.Modules.pullback (rigSection c z ε)).map
        ((τ (baseChangeSnd c ζ) (baseChangeSnd c π) g hg).inv.app (M k).L) ≫
      (sqIso (rigSection_baseChangeSnd c ε ζ)).hom.app
          ((Scheme.Modules.pullback (baseChangeSnd c π)).obj (M k).L) ≫
      (Scheme.Modules.pullback ζ.1).map (Θ c ε f M k w (baseChangeSnd c π) π.1
          (rigSection_baseChangeSnd c ε π) wT' hw).hom =
    (Θ c ε f M k z g ζ₁ S₁ ζT h₁).hom ≫ (τ ζ.1 wT' ζT hT).inv.app (EE T) := by
  have HA := half_A c ε M k π ζ g hg ζ₁ hζ₁ S₁
  have HB := half_B c ε f M k π ζ ζ₁ hζ₁
  have HC := half_C f k π wT' hw ζ ζ₁ hζ₁ ζT h₁ hT
  simp only [Θ, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp]
  dsimp only [Functor.comp_obj] at HA HB HC ⊢
  simp only [Category.assoc]
  refine ((reassoc_of% HA) _).trans ?_
  refine (congrArg (fun x => (sqIso S₁).hom.app (M k).L ≫ x) ((reassoc_of% HB) _)).trans ?_
  exact congrArg (fun x => (sqIso S₁).hom.app (M k).L ≫
      (Scheme.Modules.pullback ζ₁).map (β c ε f M k).hom ≫ x) HC

include hζ₁ in
theorem half' :
    (Scheme.Modules.pullback (rigSection c z ε)).map
        ((τ (baseChangeSnd c ζ) (baseChangeSnd c π) g hg).inv.app (M k).L) ≫
      (sqIso (rigSection_baseChangeSnd c ε ζ)).hom.app
          ((Scheme.Modules.pullback (baseChangeSnd c π)).obj (M k).L) ≫
      (Scheme.Modules.pullback ζ.1).map (Θ c ε f M k w (baseChangeSnd c π) π.1
          (rigSection_baseChangeSnd c ε π) wT' hw).hom =
    (Θ c ε f M k z g ζ₁ S₁ ζT h₁).hom ≫ (τ ζ.1 wT' ζT hT).inv.app (EE T) := by
  have HA := half_A c ε M k π ζ g hg ζ₁ hζ₁ S₁
  have HB := half_B c ε f M k π ζ ζ₁ hζ₁
  have HC := half_C f k π wT' hw ζ ζ₁ hζ₁ ζT h₁ hT
  simp only [Θ, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp]
  dsimp only [Functor.comp_obj] at HA HB HC ⊢
  simp only [Category.assoc, reassoc_of% HA, reassoc_of% HB, HC]

include hζ₁ in
theorem half_inv :
    (Scheme.Modules.pullback ζ.1).map (Θ c ε f M k w (baseChangeSnd c π) π.1
        (rigSection_baseChangeSnd c ε π) wT' hw).inv ≫
      (sqIso (rigSection_baseChangeSnd c ε ζ)).inv.app
          ((Scheme.Modules.pullback (baseChangeSnd c π)).obj (M k).L) ≫
      (Scheme.Modules.pullback (rigSection c z ε)).map
          ((τ (baseChangeSnd c ζ) (baseChangeSnd c π) g hg).hom.app (M k).L) =
    (τ ζ.1 wT' ζT hT).hom.app (EE T) ≫ (Θ c ε f M k z g ζ₁ S₁ ζT h₁).inv := by
  have H : ((Scheme.Modules.pullback (rigSection c z ε)).mapIso
        ((τ (baseChangeSnd c ζ) (baseChangeSnd c π) g hg).app (M k).L)).symm ≪≫
      (sqIso (rigSection_baseChangeSnd c ε ζ)).app
          ((Scheme.Modules.pullback (baseChangeSnd c π)).obj (M k).L) ≪≫
      (Scheme.Modules.pullback ζ.1).mapIso (Θ c ε f M k w (baseChangeSnd c π) π.1
          (rigSection_baseChangeSnd c ε π) wT' hw) =
      Θ c ε f M k z g ζ₁ S₁ ζT h₁ ≪≫ ((τ ζ.1 wT' ζT hT).app (EE T)).symm :=
    Iso.ext (half c ε f M k π wT' hw ζ g hg ζ₁ hζ₁ S₁ ζT h₁ hT)
  have H' := congrArg Iso.inv H
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.mapIso_inv,
    Category.assoc] at H'
  exact H'

end Half

theorem key (i j : ι) {Z : Scheme.{u}} {z : Z ⟶ Spec (CommRingCat.of R)}
    (ζ : SchemeHomOver z (strMap₁₂ (f i) (f j)))
    (g : Limits.pullback c z ⟶ Limits.pullback c (strMap₁₂ (f i) (f j)))
    (hg : g = baseChangeSnd c ζ)
    (g₁ : Limits.pullback c z ⟶ Limits.pullback c (u i))
    (g₂ : Limits.pullback c z ⟶ Limits.pullback c (u j))
    (hg₁ : g ≫ baseChangeSnd c (pr₁ (f i) (f j)) = g₁)
    (hg₂ : g ≫ baseChangeSnd c (pr₂ (f i) (f j)) = g₂)
    (ζ₁ : Z ⟶ U i) (ζ₂ : Z ⟶ U j)
    (hζ₁ : ζ.1 ≫ (pr₁ (f i) (f j)).1 = ζ₁) (hζ₂ : ζ.1 ≫ (pr₂ (f i) (f j)).1 = ζ₂)
    (S₁ : rigSection c z ε ≫ g₁ = ζ₁ ≫ rigSection c (u i) ε)
    (S₂ : rigSection c z ε ≫ g₂ = ζ₂ ≫ rigSection c (u j) ε)
    (ζT : Z ⟶ T) (h₁ : ζ₁ ≫ (f i).1 = ζT) (h₂ : ζ₂ ≫ (f j).1 = ζT) :
    (Scheme.Modules.pullback (rigSection c z ε)).map
      (pullHomIso (homIso c ε f M hM i j) g g₁ g₂ hg₁ hg₂).hom =
      (Θ c ε f M i z g₁ ζ₁ S₁ ζT h₁).hom ≫ (Θ c ε f M j z g₂ ζ₂ S₂ ζT h₂).inv := by
  subst hg
  have hT : ζ.1 ≫ wT f i j = ζT := by
    change ζ.1 ≫ (pr₁ (f i) (f j)).1 ≫ (f i).1 = ζT
    rw [← Category.assoc, hζ₁, h₁]
  have Hi := half c ε f M i (pr₁ (f i) (f j)) (wT f i j) rfl ζ g₁ hg₁ ζ₁ hζ₁ S₁ ζT h₁ hT
  have Hj := half_inv c ε f M j (pr₂ (f i) (f j)) (wT f i j) (pr₂_comp_eq_wT f i j)
    ζ g₂ hg₂ ζ₂ hζ₂ S₂ ζT h₂ hT
  have HN : (Scheme.Modules.pullback (rigSection c z ε)).map
        ((Scheme.Modules.pullback (baseChangeSnd c ζ)).map (homIso c ε f M hM i j).hom) =
      (sqIso (rigSection_baseChangeSnd c ε ζ)).hom.app
          ((Scheme.Modules.pullback (baseChangeSnd c (pr₁ (f i) (f j)))).obj (M i).L) ≫
        (Scheme.Modules.pullback ζ.1).map
            ((Scheme.Modules.pullback (rigSection c (strMap₁₂ (f i) (f j)) ε)).map
          (homIso c ε f M hM i j).hom) ≫
        (sqIso (rigSection_baseChangeSnd c ε ζ)).inv.app
            ((Scheme.Modules.pullback (baseChangeSnd c (pr₂ (f i) (f j)))).obj (M j).L) :=
    ((Iso.eq_comp_inv ((sqIso (rigSection_baseChangeSnd c ε ζ)).app
        ((Scheme.Modules.pullback (baseChangeSnd c (pr₂ (f i) (f j)))).obj (M j).L))).mpr
      ((sqIso (rigSection_baseChangeSnd c ε ζ)).hom.naturality (homIso c ε f M hM i j).hom)).trans
      (Category.assoc _ _ _)
  rw [pullHomIso_hom', Functor.map_comp, Functor.map_comp]
  dsimp only [Functor.comp_obj] at Hi Hj HN ⊢
  rw [HN, map_homIso, Functor.map_comp]
  simp only [Category.assoc]
  refine ((reassoc_of% Hi) _).trans ?_
  refine (congrArg (fun x => (Θ c ε f M i z g₁ ζ₁ S₁ ζT h₁).hom ≫
        (τ ζ.1 (wT f i j) ζT hT).inv.app (EE T) ≫ x)
    Hj).trans ?_
  exact congrArg (fun x => (Θ c ε f M i z g₁ ζ₁ S₁ ζT h₁).hom ≫ x)
    (Iso.inv_hom_id_app_assoc (τ ζ.1 (wT f i j) ζT hT) (EE T) (Θ c ε f M j z g₂ ζ₂ S₂ ζT h₂).inv)

/-- The diagonal map to the self-overlap as a morphism over the base. -/
def δ (i : ι) : SchemeHomOver (u i) (strMap₁₂ (f i) (f i)) :=
  ⟨pullback.lift (𝟙 _) (𝟙 _) rfl, by rw [pullback.lift_fst_assoc, Category.id_comp]⟩

lemma δ_pr₁ (i : ι) : baseChangeSnd c (δ f i) ≫ baseChangeSnd c (pr₁ (f i) (f i)) = 𝟙 _ := by
  rw [baseChangeSnd_comp]
  have e : postComp (pr₁ (f i) (f i)) (δ f i) = ⟨𝟙 _, Category.id_comp _⟩
      := Subtype.ext (pullback.lift_fst _ _ _)
  rw [e]
  exact baseChangeSnd_id c (u i)

lemma δ_pr₂ (i : ι) : baseChangeSnd c (δ f i) ≫ baseChangeSnd c (pr₂ (f i) (f i)) = 𝟙 _ := by
  rw [baseChangeSnd_comp]
  have e : postComp (pr₂ (f i) (f i)) (δ f i) = ⟨𝟙 _, Category.id_comp _⟩
      := Subtype.ext (pullback.lift_snd _ _ _)
  rw [e]
  exact baseChangeSnd_id c (u i)

lemma nonempty_rigidification (i : ι) {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    (g₁ : Limits.pullback c z ⟶ Limits.pullback c (u i)) (ζ₁ : Z ⟶ U i)
    (S₁ : rigSection c z ε ≫ g₁ = ζ₁ ≫ rigSection c (u i) ε) (ζT : Z ⟶ T) (h₁ : ζ₁ ≫ (f i).1 = ζT) :
    Nonempty
        ((Scheme.Modules.pullback (rigSection c z ε)).obj
          ((Scheme.Modules.pullback g₁).obj (M i).L) ≅
      SheafOfModules.unit Z.ringCatSheaf) :=
  ⟨Θ c ε f M i z g₁ ζ₁ S₁ ζT h₁ ≪≫ Scheme.Modules.pullbackUnitIso ζT⟩

theorem pullHomIso_self (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      let : Algebra A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤) :=
        Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)))
    (i : ι) :
    pullHomIso (homIso c ε f M hM i i) (baseChangeSnd c (δ f i)) (𝟙 _) (𝟙 _) (δ_pr₁ c f i)
        (δ_pr₂ c f i) =
      Iso.refl _ := by
  have S : rigSection c (u i) ε ≫ 𝟙 _ = 𝟙 _ ≫ rigSection c (u i) ε := by
    simp only [Category.comp_id, Category.id_comp]
  have K := key c ε f M hM i i (δ f i) _ rfl (𝟙 _) (𝟙 _) (δ_pr₁ c f i) (δ_pr₂ c f i) (𝟙 _) (𝟙 _)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) S S (f i).1
      (Category.id_comp _) (Category.id_comp _)
  exact iso_eq_of_map_rigSection_eq c ε (u i) hH0
    ((M i).isInvertible.pullback _) ((M i).isInvertible.pullback _)
    (nonempty_rigidification c ε f M i (u i) (𝟙 _) (𝟙 _) S (f i).1 (Category.id_comp _)) _ _ (by
      rw [K, Iso.hom_inv_id, Iso.refl_hom, CategoryTheory.Functor.map_id])

section comp
variable (i j k : ι)

/-- The structure map from a triple overlap to the base. -/
abbrev ζT3 : Limits.pullback (pr₂ (f i) (f j)).1 (pr₁ (f j) (f k)).1 ⟶ T :=
  (ρ₁₂ (f i) (f j) (f k)).1 ≫ wT f i j

/-- The first chart projection from the triple overlap. -/
abbrev χ₁ : Limits.pullback (pr₂ (f i) (f j)).1 (pr₁ (f j) (f k)).1 ⟶ U i :=
  (ρ₁₂ (f i) (f j) (f k)).1 ≫ (pr₁ (f i) (f j)).1
/-- The second chart projection from the triple overlap. -/
abbrev χ₂ : Limits.pullback (pr₂ (f i) (f j)).1 (pr₁ (f j) (f k)).1 ⟶ U j :=
  (ρ₁₂ (f i) (f j) (f k)).1 ≫ (pr₂ (f i) (f j)).1
/-- The third chart projection from the triple overlap. -/
abbrev χ₃ : Limits.pullback (pr₂ (f i) (f j)).1 (pr₁ (f j) (f k)).1 ⟶ U k :=
  (ρ₂₃ (f i) (f j) (f k)).1 ≫ (pr₂ (f j) (f k)).1

lemma hχ₁ : χ₁ f i j k ≫ (f i).1 = ζT3 f i j k := Category.assoc _ _ _
lemma hχ₂ : χ₂ f i j k ≫ (f j).1 = ζT3 f i j k := by
  change ((ρ₁₂ (f i) (f j) (f k)).1 ≫ (pr₂ (f i) (f j)).1) ≫ (f j).1 =
    (ρ₁₂ (f i) (f j) (f k)).1 ≫ (pr₁ (f i) (f j)).1 ≫ (f i).1
  rw [Category.assoc, pr₂_comp_eq_wT]
lemma hχ₃ : χ₃ f i j k ≫ (f k).1 = ζT3 f i j k := by
  change ((ρ₂₃ (f i) (f j) (f k)).1 ≫ (pr₂ (f j) (f k)).1) ≫ (f k).1 =
    (ρ₁₂ (f i) (f j) (f k)).1 ≫ (pr₁ (f i) (f j)).1 ≫ (f i).1
  rw [Category.assoc, pr₂_comp_eq_wT]
  change (ρ₂₃ (f i) (f j) (f k)).1 ≫ (pr₁ (f j) (f k)).1 ≫ (f j).1 = _
  rw [← Category.assoc, show (ρ₂₃ (f i) (f j) (f k)).1 ≫ (pr₁ (f j) (f k)).1 =
      (ρ₁₂ (f i) (f j) (f k)).1 ≫ (pr₂ (f i) (f j)).1 from pullback.condition.symm, Category.assoc,
    pr₂_comp_eq_wT]

lemma S₁' : rigSection c _ ε ≫ (sq₃F c f i j k).p₁ = χ₁ f i j k ≫ rigSection c (u i) ε :=
  rigSection_baseChangeSnd c ε _
lemma S₂' : rigSection c _ ε ≫ (sq₃F c f i j k).p₂ = χ₂ f i j k ≫ rigSection c (u j) ε :=
  rigSection_baseChangeSnd c ε _
lemma S₃' : rigSection c _ ε ≫ (sq₃F c f i j k).p₃ = χ₃ f i j k ≫ rigSection c (u k) ε :=
  rigSection_baseChangeSnd c ε _


theorem pullHomIso_comp (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      let : Algebra A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤) :=
        Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A
          Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤))) :
    pullHomIso (Y' := Limits.pullback c (strMap₁₂ (pr₂ (f i) (f j)) (pr₁ (f j) (f k))))
        (homIso c ε f M hM i j) (sq₃F c f i j k).p₁₂ (sq₃F c f i j k).p₁ (sq₃F c f i j k).p₂
        (sq₃F c f i j k).p₁₂_p₁ (sq₃F c f i j k).p₁₂_p₂ ≪≫
      pullHomIso (Y' := Limits.pullback c (strMap₁₂ (pr₂ (f i) (f j)) (pr₁ (f j) (f k))))
          (homIso c ε f M hM j k) (sq₃F c f i j k).p₂₃ (sq₃F c f i j k).p₂ (sq₃F c f i j k).p₃
        (sq₃F c f i j k).p₂₃_p₂ (sq₃F c f i j k).p₂₃_p₃ =
      pullHomIso (Y' := Limits.pullback c (strMap₁₂ (pr₂ (f i) (f j)) (pr₁ (f j) (f k))))
          (homIso c ε f M hM i k) (sq₃F c f i j k).p₁₃ (sq₃F c f i j k).p₁ (sq₃F c f i j k).p₃
        (sq₃F c f i j k).p₁₃_p₁ (sq₃F c f i j k).p₁₃_p₃ := by
  have K₁₂ := key c ε f M hM i j (ρ₁₂ (f i) (f j) (f k))
    (sq₃F c f i j k).p₁₂ rfl (sq₃F c f i j k).p₁ (sq₃F c f i j k).p₂
    (sq₃F c f i j k).p₁₂_p₁ (sq₃F c f i j k).p₁₂_p₂ (χ₁ f i j k) (χ₂ f i j k) rfl rfl
      (S₁' c ε f i j k) (S₂' c ε f i j k)
    (ζT3 f i j k) (hχ₁ f i j k) (hχ₂ f i j k)
  have K₂₃ := key c ε f M hM j k (ρ₂₃ (f i) (f j) (f k))
    (sq₃F c f i j k).p₂₃ rfl (sq₃F c f i j k).p₂ (sq₃F c f i j k).p₃
    (sq₃F c f i j k).p₂₃_p₂ (sq₃F c f i j k).p₂₃_p₃ (χ₂ f i j k) (χ₃ f i j k)
      pullback.condition.symm rfl
    (S₂' c ε f i j k) (S₃' c ε f i j k) (ζT3 f i j k) (hχ₂ f i j k) (hχ₃ f i j k)
  have K₁₃ := key c ε f M hM i k (ρ₁₃ (f i) (f j) (f k))
    (sq₃F c f i j k).p₁₃ rfl (sq₃F c f i j k).p₁ (sq₃F c f i j k).p₃
    (sq₃F c f i j k).p₁₃_p₁ (sq₃F c f i j k).p₁₃_p₃ (χ₁ f i j k) (χ₃ f i j k)
      (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _) (S₁' c ε f i j k) (S₃' c ε f i j k) (ζT3 f i j k)
      (hχ₁ f i j k) (hχ₃ f i j k)
  exact iso_eq_of_map_rigSection_eq c ε _ hH0
    ((M i).isInvertible.pullback _) ((M k).isInvertible.pullback _)
    (nonempty_rigidification c ε f M k _ (sq₃F c f i j k).p₃ (χ₃ f i j k)
      (S₃' c ε f i j k) (ζT3 f i j k) (hχ₃ f i j k))
    _ _ (by
      rw [Iso.trans_hom, Functor.map_comp, K₁₂, K₂₃, K₁₃]
      simp only [Category.assoc, Iso.inv_hom_id_assoc])

end comp

end Datum

end Rigidification

end AlgebraicGeometry.RelPicard.RigidifiedDescent

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Extension by summation from an over-category

An abelian presheaf on the over-category extends to the ambient category by
taking a direct sum over arrows to the chosen object.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped DirectSum

namespace CategoryTheory

universe u v

variable {C : Type v} [Category.{u} C] (U : C)

local instance (V : C) : DecidableEq (V ⟶ U) := Classical.decEq _

/-- The value of extension by summation from the over-category:
one summand for each arrow to the chosen object. -/
abbrev overAbelianExtensionObj (F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) (V : C) :
    AddCommGrpCat.{u} :=
  AddCommGrpCat.of (⨁ (h : V ⟶ U), F.obj (op (Over.mk h)))

/-- Restriction in extension by summation sends the summand at h to the
summand at g followed by h, using the original presheaf restriction. -/
def overAbelianExtensionMap (F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {V W : C} (g : V ⟶ W) :
    overAbelianExtensionObj U F W ⟶ overAbelianExtensionObj U F V := by
  classical
  exact AddCommGrpCat.ofHom (DirectSum.toAddMonoid (fun (h : W ⟶ U) =>
    (DirectSum.of (fun k : V ⟶ U => F.obj (op (Over.mk k))) (g ≫ h)).comp
      (F.map (Over.homMk (U := Over.mk (g ≫ h)) (V := Over.mk h) g rfl).op).hom))

/-- Formula for restriction on a single summand. -/
theorem overAbelianExtensionMap_of (F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {V W : C} (g : V ⟶ W) (h : W ⟶ U) (a : F.obj (op (Over.mk h))) :
    overAbelianExtensionMap U F g
      (DirectSum.of (fun k : W ⟶ U => F.obj (op (Over.mk k))) h a) =
    DirectSum.of (fun k : V ⟶ U => F.obj (op (Over.mk k))) (g ≫ h)
      (F.map (Over.homMk (U := Over.mk (g ≫ h)) (V := Over.mk h) g rfl).op a) := by
  classical
  exact DirectSum.toAddMonoid_of _ _ _

/-- The summand formula with an explicitly chosen target index avoids
dependent transports when equal composites are identified. -/
theorem overAbelianExtensionMap_of_eq (F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {V W : C} (g : V ⟶ W) (hV : V ⟶ U) (hW : W ⟶ U)
    (w : g ≫ hW = hV) (a : F.obj (op (Over.mk hW))) :
    overAbelianExtensionMap U F g
      (DirectSum.of (fun k : W ⟶ U => F.obj (op (Over.mk k))) hW a) =
    DirectSum.of (fun k : V ⟶ U => F.obj (op (Over.mk k))) hV
      (F.map (Over.homMk (U := Over.mk hV) (V := Over.mk hW) g w).op a) := by
  subst hV
  exact overAbelianExtensionMap_of U F g hW a

/-- Identity restriction for extension by summation. -/
theorem overAbelianExtensionMap_id (F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) (V : C) :
    overAbelianExtensionMap U F (𝟙 V) = 𝟙 (overAbelianExtensionObj U F V) := by
  classical
  apply AddCommGrpCat.hom_ext
  apply DirectSum.addHom_ext
  intro h a
  rw [overAbelianExtensionMap_of_eq U F (𝟙 V) h h (Category.id_comp h)]
  have hi : (Over.homMk (U := Over.mk h) (V := Over.mk h) (𝟙 V)
      (Category.id_comp h)) = 𝟙 (Over.mk h) := by
    apply Over.OverMorphism.ext
    rfl
  rw [hi, op_id, F.map_id]
  rfl

/-- Composition of restrictions for extension by summation. -/
theorem overAbelianExtensionMap_comp (F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {V W Z : C} (g : V ⟶ W) (k : W ⟶ Z) :
    overAbelianExtensionMap U F (g ≫ k) =
      overAbelianExtensionMap U F k ≫ overAbelianExtensionMap U F g := by
  classical
  apply AddCommGrpCat.hom_ext
  apply DirectSum.addHom_ext
  intro h a
  change overAbelianExtensionMap U F (g ≫ k) (DirectSum.of _ h a) =
    overAbelianExtensionMap U F g
      (overAbelianExtensionMap U F k (DirectSum.of _ h a))
  rw [overAbelianExtensionMap_of_eq U F (g ≫ k) (g ≫ k ≫ h) h
      (Category.assoc g k h), overAbelianExtensionMap_of, overAbelianExtensionMap_of]
  apply congrArg (DirectSum.of (fun t : V ⟶ U => F.obj (op (Over.mk t))) (g ≫ k ≫ h))
  have hc :
      Over.homMk (U := Over.mk (g ≫ k ≫ h)) (V := Over.mk h)
        (g ≫ k) (Category.assoc g k h) =
      Over.homMk (U := Over.mk (g ≫ k ≫ h)) (V := Over.mk (k ≫ h)) g rfl ≫
        Over.homMk (U := Over.mk (k ≫ h)) (V := Over.mk h) k rfl := by
    apply Over.OverMorphism.ext
    rfl
  rw [hc, op_comp, F.map_comp]
  rfl

/-- Extension by summation of an abelian presheaf on an over-category. -/
def overAbelianExtensionPresheaf (F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    Cᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V := overAbelianExtensionObj U F V.unop
  map g := overAbelianExtensionMap U F g.unop
  map_id V := overAbelianExtensionMap_id U F V.unop
  map_comp g k := overAbelianExtensionMap_comp U F k.unop g.unop

/-- Restriction of abelian presheaves to an over-category. -/
abbrev overAbelianRestrictionPresheaf :
    (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ AddCommGrpCat.{u}).obj (Over.forget U).op

/-- A map out of extension by summation restricts on each summand. -/
def overAbelianExtensionHomTo
    (F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) (P : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (α : overAbelianExtensionPresheaf U F ⟶ P) :
    F ⟶ (overAbelianRestrictionPresheaf U).obj P where
  app W := AddCommGrpCat.ofHom
    (DirectSum.of (fun h : W.unop.left ⟶ U => F.obj (op (Over.mk h))) W.unop.hom) ≫
      α.app (op W.unop.left)
  naturality {W Z} g := by
    apply AddCommGrpCat.ext
    intro a
    have hα := ConcreteCategory.congr_hom (α.naturality g.unop.left.op)
      (DirectSum.of (fun h : W.unop.left ⟶ U => F.obj (op (Over.mk h))) W.unop.hom a)
    change α.app (op Z.unop.left)
      (overAbelianExtensionMap U F g.unop.left
        (DirectSum.of _ W.unop.hom a)) =
      P.map g.unop.left.op (α.app (op W.unop.left)
        (DirectSum.of _ W.unop.hom a)) at hα
    rw [overAbelianExtensionMap_of_eq U F g.unop.left Z.unop.hom W.unop.hom
      (Over.w g.unop)] at hα
    have hg : Over.homMk g.unop.left (Over.w g.unop) = g.unop :=
      Over.homMk_eta g.unop _
    rw [hg, Quiver.Hom.op_unop] at hα
    exact hα

/-- A map to restriction extends uniquely by summing its components. -/
def overAbelianExtensionHomFrom
    (F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) (P : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (β : F ⟶ (overAbelianRestrictionPresheaf U).obj P) :
    overAbelianExtensionPresheaf U F ⟶ P where
  app V := AddCommGrpCat.ofHom (DirectSum.toAddMonoid
    (fun h : V.unop ⟶ U => (β.app (op (Over.mk h))).hom))
  naturality {V W} g := by
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext
    intro h a
    change DirectSum.toAddMonoid
      (fun t : W.unop ⟶ U => (β.app (op (Over.mk t))).hom)
        (overAbelianExtensionMap U F g.unop (DirectSum.of _ h a)) =
      P.map g (DirectSum.toAddMonoid
        (fun t : V.unop ⟶ U => (β.app (op (Over.mk t))).hom) (DirectSum.of _ h a))
    rw [overAbelianExtensionMap_of, DirectSum.toAddMonoid_of,
      DirectSum.toAddMonoid_of]
    exact ConcreteCategory.congr_hom
      (β.naturality (Over.homMk (U := Over.mk (g.unop ≫ h))
        (V := Over.mk h) g.unop rfl).op) a

/-- The universal property of extension by summation. -/
def overAbelianExtensionHomEquiv
    (F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (overAbelianExtensionPresheaf U F ⟶ P) ≃
      (F ⟶ (overAbelianRestrictionPresheaf U).obj P) where
  toFun := overAbelianExtensionHomTo U F P
  invFun := overAbelianExtensionHomFrom U F P
  left_inv α := by
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext
    intro h a
    exact DirectSum.toAddMonoid_of
      (fun i => (AddCommGrpCat.ofHom
        (DirectSum.of (fun t : V.unop ⟶ U => F.obj (op (Over.mk t))) i) ≫
          α.app (op V.unop)).hom) h a
  right_inv β := by
    apply NatTrans.ext
    funext W
    apply AddCommGrpCat.ext
    intro a
    change DirectSum.toAddMonoid
      (fun h : W.unop.left ⟶ U => (β.app (op (Over.mk h))).hom)
      (DirectSum.of (fun h : W.unop.left ⟶ U => F.obj (op (Over.mk h)))
        W.unop.hom a) = β.app W a
    exact DirectSum.toAddMonoid_of
      (β := fun h : W.unop.left ⟶ U => ↥(F.obj (op (Over.mk h))))
      (γ := ↥(P.obj (op W.unop.left)))
      (fun h : W.unop.left ⟶ U => (β.app (op (Over.mk h))).hom)
      W.unop.hom a

/-- Naturality of the summation universal property in its target. -/
theorem overAbelianExtensionHomEquiv_naturality
    (F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{u}}
    (α : overAbelianExtensionPresheaf U F ⟶ P) (γ : P ⟶ Q) :
    overAbelianExtensionHomEquiv U F Q (α ≫ γ) =
      overAbelianExtensionHomEquiv U F P α ≫
        (overAbelianRestrictionPresheaf U).map γ := by
  apply NatTrans.ext
  funext W
  change AddCommGrpCat.ofHom (DirectSum.of
      (fun h : W.unop.left ⟶ U => F.obj (op (Over.mk h))) W.unop.hom) ≫
      (α.app (op W.unop.left) ≫ γ.app (op W.unop.left)) =
    (AddCommGrpCat.ofHom (DirectSum.of
      (fun h : W.unop.left ⟶ U => F.obj (op (Over.mk h))) W.unop.hom) ≫
      α.app (op W.unop.left)) ≫ γ.app (op W.unop.left)
  exact (Category.assoc _ _ _).symm

/-- Extension by summation as the left adjoint of restriction. -/
def overAbelianExtension :
    ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  Adjunction.leftAdjointOfEquiv (fun F P => overAbelianExtensionHomEquiv U F P)
    (fun F _ _ γ α => overAbelianExtensionHomEquiv_naturality U F α γ)

/-- The presheaf extension/restriction adjunction. -/
def overAbelianExtensionAdjunction :
    overAbelianExtension U ⊣ overAbelianRestrictionPresheaf U :=
  Adjunction.adjunctionOfEquivLeft
    (fun F P => overAbelianExtensionHomEquiv U F P)
    (fun F _ _ γ α => overAbelianExtensionHomEquiv_naturality U F α γ)

/-- Extension acts componentwise on the summands. -/
theorem overAbelianExtension_map_app_of
    {F G : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}} (τ : F ⟶ G)
    (V : C) (h : V ⟶ U) (a : F.obj (op (Over.mk h))) :
    ((overAbelianExtension U).map τ).app (op V) (DirectSum.of _ h a) =
      DirectSum.of (fun t : V ⟶ U => G.obj (op (Over.mk t))) h
        (τ.app (op (Over.mk h)) a) := by
  change DirectSum.toAddMonoid
    (fun t : V ⟶ U =>
      (DirectSum.of (fun k : V ⟶ U => G.obj (op (Over.mk k))) t).comp
        (τ.app (op (Over.mk t))).hom) (DirectSum.of _ h a) = _
  exact DirectSum.toAddMonoid_of
    (β := fun t : V ⟶ U => ↥(F.obj (op (Over.mk t))))
    (fun t : V ⟶ U =>
      (DirectSum.of (fun k : V ⟶ U => G.obj (op (Over.mk k))) t).comp
        (τ.app (op (Over.mk t))).hom) h a

/-- The component of extension is the direct sum of the original components. -/
theorem overAbelianExtension_map_app
    {F G : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}} (τ : F ⟶ G) (V : Cᵒᵖ) :
    ((overAbelianExtension U).map τ).app V =
      AddCommGrpCat.ofHom (DirectSum.map
        (fun h : V.unop ⟶ U => (τ.app (op (Over.mk h))).hom)) := by
  apply AddCommGrpCat.hom_ext
  apply DirectSum.addHom_ext
  intro h a
  change ((overAbelianExtension U).map τ).app V (DirectSum.of _ h a) =
    DirectSum.map (fun t : V.unop ⟶ U => (τ.app (op (Over.mk t))).hom)
      (DirectSum.of _ h a)
  rw [overAbelianExtension_map_app_of]
  exact (DirectSum.map_of
    (α := fun t : V.unop ⟶ U => ↥(F.obj (op (Over.mk t))))
    (β := fun t : V.unop ⟶ U => ↥(G.obj (op (Over.mk t))))
    (fun t : V.unop ⟶ U => (τ.app (op (Over.mk t))).hom) h a).symm

/-- Summation over the maps to the base object preserves monomorphisms. -/
instance overAbelianExtension_preservesMonomorphisms :
    (overAbelianExtension U).PreservesMonomorphisms where
  preserves {F G} τ _ := by
    have h : ∀ V, Mono (((overAbelianExtension U).map τ).app V) := by
      intro V
      rw [overAbelianExtension_map_app]
      apply ConcreteCategory.mono_of_injective
      apply (DirectSum.map_injective _).mpr
      intro t
      exact (AddCommGrpCat.mono_iff_injective (τ.app (op (Over.mk t)))).mp inferInstance
    exact NatTrans.mono_of_mono_app _

section Sheaves

open Limits

variable (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{u}]
variable [HasSheafify (J.over U) AddCommGrpCat.{u}]

/-- Extension by summation, followed by sheafification on the original site. -/
def overAbelianSheafExtension :
    Sheaf (J.over U) AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u} :=
  sheafToPresheaf (J.over U) AddCommGrpCat.{u} ⋙
    overAbelianExtension U ⋙ presheafToSheaf J AddCommGrpCat.{u}

/-- Extension is left adjoint to the actual restriction to the localized site. -/
def overAbelianSheafExtensionAdjunction :
    overAbelianSheafExtension U J ⊣ J.overPullback AddCommGrpCat.{u} U :=
  ((overAbelianExtensionAdjunction U).comp
    (sheafificationAdjunction J AddCommGrpCat.{u})).restrictFullyFaithful
      (fullyFaithfulSheafToPresheaf (J.over U) AddCommGrpCat.{u})
      (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

instance overAbelianSheafExtension_isLeftAdjoint :
    (overAbelianSheafExtension U J).IsLeftAdjoint :=
  (overAbelianSheafExtensionAdjunction U J).isLeftAdjoint

instance overAbelianSheafExtension_preservesMonomorphisms :
    (overAbelianSheafExtension U J).PreservesMonomorphisms := by
  dsimp only [overAbelianSheafExtension]
  infer_instance

instance overAbelianSheafExtension_additive :
    (overAbelianSheafExtension U J).Additive := by
  have : PreservesBinaryBiproducts (overAbelianSheafExtension U J) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Extension is exact; the monomorphism assertion comes from direct sums. -/
instance overAbelianSheafExtension_preservesFiniteLimits :
    PreservesFiniteLimits (overAbelianSheafExtension U J) := by
  have : (overAbelianSheafExtension U J).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  exact Functor.preservesFiniteLimits_of_preservesHomology _

instance overAbelianSheafRestriction_isRightAdjoint :
    (J.overPullback AddCommGrpCat.{u} U).IsRightAdjoint :=
  (overAbelianSheafExtensionAdjunction U J).isRightAdjoint

instance overAbelianSheafRestriction_additive :
    (J.overPullback AddCommGrpCat.{u} U).Additive := by
  have : PreservesBinaryBiproducts (J.overPullback AddCommGrpCat.{u} U) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Restriction to the localized site preserves injectives because its
constructed left adjoint is exact. -/
instance overAbelianSheafRestriction_preservesInjectiveObjects :
    (J.overPullback AddCommGrpCat.{u} U).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (overAbelianSheafExtensionAdjunction U J)

/-- With products on the site, restriction also has its geometric right adjoint. -/
instance overAbelianSheafRestriction_isLeftAdjoint [HasBinaryProducts C] :
    (J.overPullback AddCommGrpCat.{u} U).IsLeftAdjoint :=
  ((Over.forgetAdjStar U).sheafPushforwardContinuous
    (E := AddCommGrpCat.{u}) (J.over U) J).isLeftAdjoint

end Sheaves

end CategoryTheory

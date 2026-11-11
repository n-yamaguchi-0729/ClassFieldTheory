/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Graphs of a labelled action and exact change of base

The graph pairing of a family of endomorphisms is compatible with the native
coproduct and product comparisons. For a finite group action, invertibility
of this pairing is the torsor condition. Exact functors preserve this
condition, and an equivariant isomorphism preserves the original labels.
-/

@[expose] public section

noncomputable section

universe u v u' v' w

open CategoryTheory Limits

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {G : Type w}

/-- The sum of the graphs of a labelled family of endomorphisms. -/
def graphFamilyMap {X : C} [HasCoproduct (fun _ : G => X)] [HasBinaryProduct X X]
    (a : G → (X ⟶ X)) : (∐ fun _ : G => X) ⟶ X ⨯ X :=
  Sigma.desc (fun g => prod.lift (𝟙 X) (a g))

/-- The graph pairing commutes with the actual coproduct and product
comparison maps of a functor. -/
theorem graphFamilyMap_map (F : C ⥤ D) {X : C}
    [HasCoproduct (fun _ : G => X)] [HasBinaryProduct X X]
    [HasCoproduct (fun _ : G => F.obj X)] [HasBinaryProduct (F.obj X) (F.obj X)]
    (a : G → (X ⟶ X)) :
    sigmaComparison F (fun _ : G => X) ≫
        F.map (graphFamilyMap a) ≫ prodComparison F X X =
      graphFamilyMap (fun g => F.map (a g)) := by
  apply Sigma.hom_ext
  intro g
  apply prod.hom_ext
  · simp only [graphFamilyMap, Category.assoc, ι_comp_sigmaComparison_assoc,
      prodComparison_fst, ← F.map_comp, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc,
      prod.lift_fst, F.map_id]
  · simp only [graphFamilyMap, Category.assoc, ι_comp_sigmaComparison_assoc,
      prodComparison_snd, ← F.map_comp, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc,
      prod.lift_snd]

/-- The canonical comparisons identify invertibility of the mapped graph with that of
the graph of the mapped family. This statement does not assert that `F` reflects isomorphisms. -/
theorem graphFamilyMap_map_isIso_iff (F : C ⥤ D) {X : C}
    [HasCoproduct (fun _ : G => X)] [HasBinaryProduct X X]
    [HasCoproduct (fun _ : G => F.obj X)] [HasBinaryProduct (F.obj X) (F.obj X)]
    [PreservesColimit (Discrete.functor (fun _ : G => X)) F]
    [PreservesLimit (pair X X) F] (a : G → (X ⟶ X)) :
    IsIso (F.map (graphFamilyMap a)) ↔
      IsIso (graphFamilyMap (fun g => F.map (a g))) := by
  rw [← graphFamilyMap_map F a, isIso_comp_left_iff, isIso_comp_right_iff]

/-- An equivariant change of object respects every graph coordinate. -/
theorem graphFamilyMap_naturality {X Y : C}
    [HasCoproduct (fun _ : G => X)] [HasBinaryProduct X X]
    [HasCoproduct (fun _ : G => Y)] [HasBinaryProduct Y Y]
    (a : G → (X ⟶ X)) (b : G → (Y ⟶ Y)) (f : X ⟶ Y)
    (hf : ∀ g, a g ≫ f = f ≫ b g) :
    Sigma.map (fun _ : G => f) ≫ graphFamilyMap b =
      graphFamilyMap a ≫ prod.map f f := by
  apply Sigma.hom_ext
  intro g
  apply prod.hom_ext
  · simp only [graphFamilyMap, Category.assoc, Sigma.ι_map_assoc,
      Sigma.ι_comp_desc_assoc, prod.lift_fst, prod.lift_fst_assoc, prod.map_fst,
      Category.id_comp, Category.comp_id]
  · simp only [graphFamilyMap, Category.assoc, Sigma.ι_map_assoc,
      Sigma.ι_comp_desc_assoc, prod.lift_snd, prod.lift_snd_assoc, prod.map_snd, hf g]

/-- An equivariant isomorphism transports the torsor pairing, without
replacing the original action by an unlabelled isomorphic action. -/
theorem graphFamilyMap_isIso_of_equivariant_iso {X Y : C}
    [HasCoproductsOfShape G C] [HasBinaryProduct X X] [HasBinaryProduct Y Y]
    (a : G → (X ⟶ X)) (b : G → (Y ⟶ Y)) (e : X ≅ Y)
    (he : ∀ g, a g ≫ e.hom = e.hom ≫ b g)
    [IsIso (graphFamilyMap b)] : IsIso (graphFamilyMap a) := by
  have h : IsIso (Sigma.map (fun _ : G => e.hom) ≫ graphFamilyMap b) := inferInstance
  rw [graphFamilyMap_naturality a b e.hom he] at h
  exact (isIso_comp_right_iff (graphFamilyMap a) (prod.map e.hom e.hom)).mp h

end CategoryTheory.Limits

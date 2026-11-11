/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FreeAbelianCechAllDegrees
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Actual representable terms of the free Cech complex

The pointwise free Cech terms of a representable presheaf are the free
abelian representables of the actual finite powers. This identifies their
morphisms into a sheaf with actual sections on those powers.
-/

@[expose] public section

noncomputable section
universe u v
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace EtaleCohomology

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]

/-- The actual vertex tuple in a Cech nerve of a set. -/
def setCechVerticesEquiv (A : Type v) (n : ℕ) :
    (Arrow.mk (terminal.from A)).cechNerve.obj (op ⦋n⦌) ≃
      (Fin (n + 1) → A) :=
  (CechNerveTerminalFrom.wideCospan.limitIsoPi (Fin (n + 1)) A).toEquiv.trans
    (Types.productIso (fun _ : Fin (n + 1) => A)).toEquiv

/-- A coordinate of the tuple is its actual wide-pullback projection. -/
theorem setCechVerticesEquiv_apply (A : Type v) (n : ℕ)
    (z : (Arrow.mk (terminal.from A)).cechNerve.obj (op ⦋n⦌))
    (i : Fin (n + 1)) :
    setCechVerticesEquiv A n z i =
      (WidePullback.π (B := ⊤_ (Type v)) (objs := fun _ : Fin (n + 1) => A)
        (arrows := fun _ => terminal.from A) i) z := by
  exact ConcreteCategory.congr_hom
    (CechNerveTerminalFrom.wideCospan.limitIsoPi_hom_comp_pi
      (Fin (n + 1)) A i) z

/-- Tuples of morphisms are morphisms into the actual finite product. -/
def finitePowerHomEquiv (T X : C) (n : ℕ) :
    (Fin (n + 1) → (T ⟶ X)) ≃ (T ⟶ ∏ᶜ fun _ : Fin (n + 1) => X) where
  toFun p := Pi.lift p
  invFun a i := a ≫ Pi.π _ i
  left_inv p := by
    funext i
    exact Pi.lift_comp_π p i
  right_inv a := by
    apply Pi.hom_ext
    intro i
    exact Pi.lift_comp_π _ i

/-- Actual Cech vertices of a representable are represented by the
actual finite power, without choosing a splitting of a geometric cover. -/
def representableCechVerticesEquiv (T X : C) (n : ℕ) :
    (Arrow.mk (terminal.from (T ⟶ X))).cechNerve.obj (op ⦋n⦌) ≃
      (T ⟶ ∏ᶜ fun _ : Fin (n + 1) => X) :=
  (setCechVerticesEquiv (T ⟶ X) n).trans (finitePowerHomEquiv T X n)

/-- The representable identification respects every coordinate. -/
theorem representableCechVerticesEquiv_comp_π (T X : C) (n : ℕ)
    (z : (Arrow.mk (terminal.from (T ⟶ X))).cechNerve.obj (op ⦋n⦌))
    (i : Fin (n + 1)) :
    representableCechVerticesEquiv T X n z ≫ Pi.π _ i =
      (WidePullback.π (B := ⊤_ (Type v))
        (objs := fun _ : Fin (n + 1) => (T ⟶ X))
        (arrows := fun _ => terminal.from (T ⟶ X)) i) z := by
  exact (Pi.lift_comp_π _ i).trans (setCechVerticesEquiv_apply _ n z i)

/-- Coordinate extraction commutes with a map of vertex sets. -/
theorem setCechVerticesEquiv_map {A B : Type v} (f : A → B) (n : ℕ)
    (z : (Arrow.mk (terminal.from A)).cechNerve.obj (op ⦋n⦌))
    (i : Fin (n + 1)) :
    setCechVerticesEquiv B n
      ((Arrow.mapCechNerve
        (Arrow.homMk (f := Arrow.mk (terminal.from A))
          (g := Arrow.mk (terminal.from B)) (↾f) (𝟙 _) (terminal.hom_ext _ _))).app
        (op ⦋n⦌) z) i =
      f (setCechVerticesEquiv A n z i) := by
  rw [setCechVerticesEquiv_apply, setCechVerticesEquiv_apply]
  exact ConcreteCategory.congr_hom
    (WidePullback.lift_π (C := Type v)
      (fun _ : Fin (n + 1) => terminal.from B) _ _ _ i) z

/-- The actual free Cech term of a representable presheaf is the free
abelian representable of its actual finite power. -/
def freeAbelianRepresentableCechTermIso (X : C) (n : ℕ) :
    (freeAbelianPresheafCechComplex (yoneda.obj X)).X n ≅
      yoneda.obj (∏ᶜ fun _ : Fin (n + 1) => X) ⋙ AddCommGrpCat.free :=
  NatIso.ofComponents
    (fun T => AddCommGrpCat.free.mapIso
      (representableCechVerticesEquiv T.unop X n).toIso)
    (fun {T U} g => by
      apply AddCommGrpCat.hom_ext
      apply FreeAbelianGroup.lift_ext
      intro z
      change (Arrow.mk (terminal.from (T.unop ⟶ X))).cechNerve.obj (op ⦋n⦌) at z
      change FreeAbelianGroup.of
          (representableCechVerticesEquiv U.unop X n
            ((Arrow.mapCechNerve
              (Arrow.homMk
                (f := Arrow.mk (terminal.from (T.unop ⟶ X)))
                (g := Arrow.mk (terminal.from (U.unop ⟶ X)))
                (↾fun a => g.unop ≫ a) (𝟙 _) (terminal.hom_ext _ _))).app
                (op ⦋n⦌) z)) =
        FreeAbelianGroup.of (g.unop ≫ representableCechVerticesEquiv T.unop X n z)
      apply congrArg FreeAbelianGroup.of
      apply Pi.hom_ext
      intro i
      change (Pi.lift (setCechVerticesEquiv (U.unop ⟶ X) n _)) ≫ Pi.π _ i =
        (g.unop ≫ Pi.lift (setCechVerticesEquiv (T.unop ⟶ X) n z)) ≫ Pi.π _ i
      rw [Pi.lift_comp_π, Category.assoc, Pi.lift_comp_π]
      exact setCechVerticesEquiv_map (fun a => g.unop ≫ a) n z i)

/-- Morphisms from an actual sheafified Cech term are actual sections
on the corresponding geometric power. -/
def freeAbelianRepresentableCechSectionsEquiv (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] (X : C)
    (I : Sheaf J AddCommGrpCat.{v}) (n : ℕ) :
    ((presheafToSheaf J AddCommGrpCat.{v}).obj
      ((freeAbelianPresheafCechComplex (yoneda.obj X)).X n) ⟶ I) ≃
      I.obj.obj (op (∏ᶜ fun _ : Fin (n + 1) => X)) :=
  (Iso.homCongr ((presheafToSheaf J AddCommGrpCat.{v}).mapIso
    (freeAbelianRepresentableCechTermIso X n)) (Iso.refl I)).trans
      (freeAbelianSheafYonedaHomEquiv J _ I)

/-- Reindexing actual Cech vertices agrees with reindexing coordinates. -/
theorem setCechVerticesEquiv_reindex (A : Type v)
    {m n : SimplexCategory} (f : m ⟶ n)
    (z : (Arrow.mk (terminal.from A)).cechNerve.obj (op n))
    (i : Fin (m.len + 1)) :
    setCechVerticesEquiv A m.len
        ((Arrow.mk (terminal.from A)).cechNerve.map f.op z) i =
      setCechVerticesEquiv A n.len z (f.toOrderHom i) := by
  rw [setCechVerticesEquiv_apply, setCechVerticesEquiv_apply]
  exact ConcreteCategory.congr_hom
    (WidePullback.lift_π (C := Type v)
      (fun _ : Fin (m.len + 1) => terminal.from A) _ _ _ i) z

/-- Reindexing representable Cech vertices is composition with the
actual map between the geometric powers. -/
theorem representableCechVerticesEquiv_reindex (T X : C)
    {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (z : (Arrow.mk (terminal.from (T ⟶ X))).cechNerve.obj (op ⦋n⦌)) :
    representableCechVerticesEquiv T X m
      ((Arrow.mk (terminal.from (T ⟶ X))).cechNerve.map f.op z) =
        representableCechVerticesEquiv T X n z ≫
          (cechNerveTerminalFrom X).map f.op := by
  apply Pi.hom_ext
  intro i
  change (Pi.lift (setCechVerticesEquiv (T ⟶ X) m _)) ≫ Pi.π _ i =
    (Pi.lift (setCechVerticesEquiv (T ⟶ X) n z) ≫
      Pi.lift (fun j => Pi.π (fun _ : Fin (n + 1) => X) (f.toOrderHom j))) ≫ Pi.π _ i
  rw [Pi.lift_comp_π, Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π]
  exact setCechVerticesEquiv_reindex (T ⟶ X) f z i

/-- The actual projection omitting one coordinate of a geometric
finite power. -/
def geometricCechFace (X : C) (n : ℕ) (i : Fin (n + 2)) :
    (∏ᶜ fun _ : Fin (n + 2) => X) ⟶ ∏ᶜ fun _ : Fin (n + 1) => X :=
  Pi.lift fun j => Pi.π _ (i.succAbove j)

/-- The actual free abelian representable Cech complex of geometric
finite powers. -/
def freeRepresentableCechComplex (X : C) :
    ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ℕ :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj
    (cechNerveTerminalFrom X ⋙ yoneda ⋙
      (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free)

/-- The coordinate identification respects the actual alternating
differentials in all degrees. -/
theorem freeAbelianRepresentableCechTermIso_d (X : C) (n : ℕ) :
    (freeAbelianRepresentableCechTermIso X (n + 1)).hom ≫
        (freeRepresentableCechComplex X).d (n + 1) n =
      (freeAbelianPresheafCechComplex (yoneda.obj X)).d (n + 1) n ≫
        (freeAbelianRepresentableCechTermIso X n).hom := by
  apply NatTrans.ext
  funext T
  have hs :
      ((freeAbelianPresheafCechComplex (yoneda.obj X)).d (n + 1) n).app T =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          AddCommGrpCat.free.map
            ((Arrow.mk (terminal.from (T.unop ⟶ X))).cechNerve.δ i) :=
    AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq
      ((Arrow.mk (terminal.from (T.unop ⟶ X))).cechNerve ⋙ AddCommGrpCat.free) n
  have ht :
      ((freeRepresentableCechComplex X).d (n + 1) n).app T =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          (AddCommGrpCat.free.map
            (show (T.unop ⟶ ∏ᶜ fun _ : Fin (n + 2) => X) ⟶
                (T.unop ⟶ ∏ᶜ fun _ : Fin (n + 1) => X) from
              ↾fun a => a ≫ geometricCechFace X n i) :
            AddCommGrpCat.free.obj (T.unop ⟶ ∏ᶜ fun _ : Fin (n + 2) => X) ⟶
              AddCommGrpCat.free.obj (T.unop ⟶ ∏ᶜ fun _ : Fin (n + 1) => X)) := by
    dsimp only [freeRepresentableCechComplex]
    rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
    simp only [NatTrans.app_sum, NatTrans.app_zsmul]
    rfl
  change (freeAbelianRepresentableCechTermIso X (n + 1)).hom.app T ≫
      ((freeRepresentableCechComplex X).d (n + 1) n).app T =
    ((freeAbelianPresheafCechComplex (yoneda.obj X)).d (n + 1) n).app T ≫
      (freeAbelianRepresentableCechTermIso X n).hom.app T
  let A₁ : Type v := (Arrow.mk (terminal.from (T.unop ⟶ X))).cechNerve.obj (op ⦋n + 1⦌)
  let A₀ : Type v := (Arrow.mk (terminal.from (T.unop ⟶ X))).cechNerve.obj (op ⦋n⦌)
  let B₁ : Type v := T.unop ⟶ ∏ᶜ fun _ : Fin (n + 2) => X
  let B₀ : Type v := T.unop ⟶ ∏ᶜ fun _ : Fin (n + 1) => X
  let e₁ : AddCommGrpCat.free.obj A₁ ⟶ AddCommGrpCat.free.obj B₁ :=
    (freeAbelianRepresentableCechTermIso X (n + 1)).hom.app T
  let e₀ : AddCommGrpCat.free.obj A₀ ⟶ AddCommGrpCat.free.obj B₀ :=
    (freeAbelianRepresentableCechTermIso X n).hom.app T
  let α : AddCommGrpCat.free.obj A₁ ⟶ AddCommGrpCat.free.obj A₀ :=
    ((freeAbelianPresheafCechComplex (yoneda.obj X)).d (n + 1) n).app T
  let β : AddCommGrpCat.free.obj B₁ ⟶ AddCommGrpCat.free.obj B₀ :=
    ((freeRepresentableCechComplex X).d (n + 1) n).app T
  have hα : α = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      AddCommGrpCat.free.map
        ((Arrow.mk (terminal.from (T.unop ⟶ X))).cechNerve.δ i) := hs
  have hβ : β = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      AddCommGrpCat.free.map (↾fun a : B₁ => a ≫ geometricCechFace X n i) := ht
  change e₁ ≫ β = α ≫ e₀
  rw [hα, hβ, Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  congr 1
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro z
  change FreeAbelianGroup.of
      (representableCechVerticesEquiv T.unop X (n + 1) z ≫
        (cechNerveTerminalFrom X).δ i) =
    FreeAbelianGroup.of (representableCechVerticesEquiv T.unop X n
      ((Arrow.mk (terminal.from (T.unop ⟶ X))).cechNerve.δ i z))
  exact congrArg FreeAbelianGroup.of
    (representableCechVerticesEquiv_reindex T.unop X (SimplexCategory.δ i) z).symm

/-- The pointwise free Cech complex is the actual geometric
representable Cech complex, including its differentials. -/
def freeAbelianRepresentableCechComplexIso (X : C) :
    freeAbelianPresheafCechComplex (yoneda.obj X) ≅ freeRepresentableCechComplex X :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => freeAbelianRepresentableCechTermIso X n) (by
      intro i j hij
      simp only [ComplexShape.down_Rel] at hij
      subst i
      exact freeAbelianRepresentableCechTermIso_d X j)

/-- Actual geometric free representable Cech complexes are exact in
all positive degrees before sheafification. -/
theorem freeRepresentableCechComplex_exactAt_succ (X : C) (n : ℕ) :
    (freeRepresentableCechComplex X).ExactAt (n + 1) :=
  (freeAbelianPresheafCechComplex_exactAt_succ (yoneda.obj X) n).of_iso
    (freeAbelianRepresentableCechComplexIso X)

/-- Actual sheafification preserves the positive-degree exactness of
the geometric free representable Cech complex. -/
theorem freeRepresentableCechComplex_sheaf_exactAt_succ
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]
    (X : C) (n : ℕ) :
    (((freeRepresentableCechComplex X).sc (n + 1)).map
      (presheafToSheaf J AddCommGrpCat.{v})).Exact :=
  (freeRepresentableCechComplex_exactAt_succ X n).map _

/-- Under actual evaluation, the free geometric Cech differential is
the alternating sum of restrictions to geometric faces. -/
theorem freeRepresentableCech_d_eval
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]
    (X : C) (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ)
    (a : (freeAbelianSheafYoneda J).obj
      (∏ᶜ fun _ : Fin (n + 1) => X) ⟶ F) :
    freeAbelianSheafYonedaHomAddEquiv J _ F
      ((presheafToSheaf J AddCommGrpCat.{v}).map
        ((freeRepresentableCechComplex X).d (n + 1) n) ≫ a) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        F.obj.map ((cechNerveTerminalFrom X).δ i).op
          (freeAbelianSheafYonedaHomAddEquiv J _ F a) := by
  dsimp only [freeRepresentableCechComplex]
  erw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq,
    Functor.map_sum, Preadditive.sum_comp, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  erw [Functor.map_zsmul, Preadditive.zsmul_comp, map_zsmul]
  congr 1
  exact freeAbelianSheafYonedaHomEquiv_precomp J
    ((cechNerveTerminalFrom X).δ i) F a

/-- Every positive-degree actual geometric Cech cocycle with injective
sheaf coefficients is an actual geometric Cech coboundary. -/
theorem exists_injective_geometricCech_primitive
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]
    (X : C) (I : Sheaf J AddCommGrpCat.{v}) [Injective I] (n : ℕ)
    (z : I.obj.obj (op (∏ᶜ fun _ : Fin (n + 2) => X)))
    (hz : ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) •
      I.obj.map ((cechNerveTerminalFrom X).δ i).op z = 0) :
    ∃ b : I.obj.obj (op (∏ᶜ fun _ : Fin (n + 1) => X)),
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        I.obj.map ((cechNerveTerminalFrom X).δ i).op b = z := by
  let Q := presheafToSheaf J AddCommGrpCat.{v}
  let K := freeRepresentableCechComplex X
  let a : (freeAbelianSheafYoneda J).obj
      (∏ᶜ fun _ : Fin (n + 2) => X) ⟶ I :=
    (freeAbelianSheafYonedaHomAddEquiv J _ I).symm z
  have ha : Q.map (K.d (n + 2) (n + 1)) ≫ a = 0 := by
    apply (freeAbelianSheafYonedaHomAddEquiv J
      (∏ᶜ fun _ : Fin (n + 3) => X) I).injective
    have hv := freeRepresentableCech_d_eval J X I (n + 1) a
    have hz' : (∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) •
        I.obj.map ((cechNerveTerminalFrom X).δ i).op
          (freeAbelianSheafYonedaHomAddEquiv J
            (∏ᶜ fun _ : Fin (n + 2) => X) I a)) = 0 := by
      change (∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) •
        I.obj.map ((cechNerveTerminalFrom X).δ i).op
          ((freeAbelianSheafYonedaHomAddEquiv J _ I)
            ((freeAbelianSheafYonedaHomAddEquiv J _ I).symm z))) = 0
      erw [AddEquiv.apply_symm_apply]
      exact hz
    exact hv.trans (hz'.trans
      (map_zero (freeAbelianSheafYonedaHomAddEquiv J
        (∏ᶜ fun _ : Fin (n + 3) => X) I)).symm)
  have hS : ((K.sc' (n + 2) (n + 1) n).map Q).Exact :=
    ((K.exactAt_iff' (n + 2) (n + 1) n
      ((ComplexShape.down ℕ).prev_eq'
        (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) from rfl))
      ((ComplexShape.down ℕ).next_eq'
        (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl))).mp
      (freeRepresentableCechComplex_exactAt_succ X n)).map Q
  let b : (freeAbelianSheafYoneda J).obj
      (∏ᶜ fun _ : Fin (n + 1) => X) ⟶ I :=
    hS.descToInjective a ha
  have hb : Q.map (K.d (n + 1) n) ≫ b = a :=
    hS.comp_descToInjective a ha
  refine ⟨freeAbelianSheafYonedaHomAddEquiv J _ I b, ?_⟩
  exact (freeRepresentableCech_d_eval J X I n b).symm.trans
    ((congrArg (freeAbelianSheafYonedaHomAddEquiv J
      (∏ᶜ fun _ : Fin (n + 2) => X) I) hb).trans
        ((freeAbelianSheafYonedaHomAddEquiv J _ I).apply_symm_apply z))

end EtaleCohomology

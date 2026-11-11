/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Positive-degree exactness of the free Cech complex

The free abelian Cech complex of a set is exact in every positive degree.
For a nonempty set, the existing extra-degeneracy contraction applies.
For an empty set, every term is zero. This pointwise calculation is used
for the actual free Cech resolution of sheaves.
-/

@[expose] public section

noncomputable section
universe u v w
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace EtaleCohomology

/-- The actual alternating free abelian complex of the Cech nerve of
the map from a set to the terminal set. -/
def freeAbelianSetCechComplex (A : Type u) : ChainComplex AddCommGrpCat.{u} ℕ :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj
    ((Arrow.mk (terminal.from A)).cechNerve ⋙ AddCommGrpCat.free)

/-- The free Cech complex of any set is exact in every positive degree,
without requiring that the set have a global element. -/
theorem freeAbelianSetCechComplex_exactAt_succ (A : Type u) (n : ℕ) :
    (freeAbelianSetCechComplex A).ExactAt (n + 1) := by
  classical
  cases isEmpty_or_nonempty A with
  | inl hA =>
    let a : Arrow (Type u) := Arrow.mk (terminal.from A)
    have : IsEmpty (a.cechNerve.obj (op ⦋n + 1⦌)) :=
      ⟨fun z => isEmptyElim
        ((WidePullback.π (B := ⊤_ (Type u))
          (objs := fun _ : Fin (n + 2) => A)
          (arrows := fun _ => terminal.from A) 0) z)⟩
    apply ShortComplex.exact_of_isZero_X₂
    change IsZero (AddCommGrpCat.of
      (FreeAbelianGroup (a.cechNerve.obj (op ⦋n + 1⦌))))
    exact AddCommGrpCat.isZero_of_subsingleton _
  | inr hA =>
    let a : Arrow (Type u) := Arrow.mk (terminal.from A)
    let s : SplitEpi a.hom :=
      { section_ := ↾fun _ => Classical.choice hA
        id := by
          apply terminal.hom_ext }
    let ed := (Arrow.AugmentedCechNerve.extraDegeneracy a s).map AddCommGrpCat.free
    have hz :
        IsZero (((ChainComplex.single₀ AddCommGrpCat.{u}).obj
          (AddCommGrpCat.free.obj (⊤_ (Type u)))).homology (n + 1)) :=
      (ChainComplex.exactAt_succ_single_obj _ n).isZero_homology
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
      (hz.of_iso (ed.homotopyEquiv.toHomologyIso (n + 1)))

/-- The functor assigning to a set its arrow to the terminal set. -/
def setTerminalArrow : Type u ⥤ Arrow (Type u) where
  obj A := Arrow.mk (terminal.from A)
  map f := Arrow.homMk f (𝟙 _) (terminal.hom_ext _ _)
  map_id A := by
    ext <;> rfl
  map_comp f g := by
    ext <;> rfl

/-- Functoriality of the actual free abelian Cech complex in its set of
vertices. -/
def freeAbelianSetCechComplexFunctor : Type u ⥤ ChainComplex AddCommGrpCat.{u} ℕ :=
  setTerminalArrow ⋙ SimplicialObject.cechNerve ⋙
    (SimplicialObject.whiskering (Type u) AddCommGrpCat.{u}).obj AddCommGrpCat.free ⋙
      AlgebraicTopology.alternatingFaceMapComplex AddCommGrpCat.{u}

/-- The degreewise free Cech complex of a presheaf of sets. -/
def freeAbelianPresheafCechComplex {C : Type v} [Category.{w} C]
    (P : C ⥤ Type u) : ChainComplex (C ⥤ AddCommGrpCat.{u}) ℕ where
  X n := P ⋙ freeAbelianSetCechComplexFunctor ⋙
    HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.down ℕ) n
  d i j :=
    { app V := (freeAbelianSetCechComplexFunctor.obj (P.obj V)).d i j
      naturality {_ _} g :=
        (freeAbelianSetCechComplexFunctor.map (P.map g)).comm i j }
  shape i j hij := by
    apply NatTrans.ext
    funext V
    exact (freeAbelianSetCechComplexFunctor.obj (P.obj V)).shape i j hij
  d_comp_d' i j k _ _ := by
    apply NatTrans.ext
    funext V
    exact (freeAbelianSetCechComplexFunctor.obj (P.obj V)).d_comp_d i j k

/-- Exactness in every positive degree holds pointwise before
sheafification; it does not require a presheaf-level choice of vertices. -/
theorem freeAbelianPresheafCechComplex_exactAt_succ
    {C : Type v} [Category.{w} C] (P : C ⥤ Type u) (n : ℕ) :
    (freeAbelianPresheafCechComplex P).ExactAt (n + 1) := by
  let S := (freeAbelianPresheafCechComplex P).sc (n + 1)
  have hV (V : C) : (S.map ((evaluation C AddCommGrpCat.{u}).obj V)).Exact :=
    freeAbelianSetCechComplex_exactAt_succ (P.obj V) n
  change S.Exact
  rw [S.exact_iff_iCycles_pOpcycles_zero]
  apply NatTrans.ext
  funext V
  exact (hV V).comp_eq_zero
    (congrArg (fun k => k.app V) S.iCycles_g)
    (congrArg (fun k => k.app V) S.f_pOpcycles)

/-- Actual exact sheafification preserves all positive-degree Cech
relations, not just the edge-and-triangle portion. -/
theorem freeAbelianPresheafCechComplex_sheaf_exactAt_succ
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] (P : Cᵒᵖ ⥤ Type u) (n : ℕ) :
    (((freeAbelianPresheafCechComplex P).sc (n + 1)).map
      (presheafToSheaf J AddCommGrpCat.{u})).Exact :=
  (freeAbelianPresheafCechComplex_exactAt_succ P n).map
    (presheafToSheaf J AddCommGrpCat.{u})

/-- Every positive-degree cocycle on the actual sheafified free Cech
complex has a primitive with injective coefficients. -/
theorem exists_injective_freeAbelianCech_primitive
    {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] (P : Cᵒᵖ ⥤ Type u)
    (I : Sheaf J AddCommGrpCat.{u}) [Injective I] (n : ℕ)
    (z : (presheafToSheaf J AddCommGrpCat.{u}).obj
      ((freeAbelianPresheafCechComplex P).sc (n + 1)).X₂ ⟶ I)
    (hz : (presheafToSheaf J AddCommGrpCat.{u}).map
      ((freeAbelianPresheafCechComplex P).sc (n + 1)).f ≫ z = 0) :
    ∃ b : (presheafToSheaf J AddCommGrpCat.{u}).obj
        ((freeAbelianPresheafCechComplex P).sc (n + 1)).X₃ ⟶ I,
      (presheafToSheaf J AddCommGrpCat.{u}).map
        ((freeAbelianPresheafCechComplex P).sc (n + 1)).g ≫ b = z :=
  ⟨(freeAbelianPresheafCechComplex_sheaf_exactAt_succ J P n).descToInjective z hz,
    (freeAbelianPresheafCechComplex_sheaf_exactAt_succ J P n).comp_descToInjective z hz⟩

end EtaleCohomology

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Pointwise exactness in abelian functor categories

Exactness is detected by all evaluation functors. This packages the
homology comparison once, without expanding a concrete presheaf's
definition inside its kernel proof.
-/

@[expose] public section

noncomputable section
universe v u v' u'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] [Abelian D]

/-- A short complex of functors is exact if every evaluation is exact. -/
theorem exact_of_evaluation (S : ShortComplex (C ⥤ D))
    (h : ∀ X : C, (S.map ((evaluation C D).obj X)).Exact) : S.Exact := by
  rw [exact_iff_isZero_homology]
  apply (IsZero.iff_id_eq_zero S.homology).mpr
  apply NatTrans.ext
  funext X
  let E := (evaluation C D).obj X
  have hz := (exact_iff_isZero_homology (S.map E)).mp (h X)
  have hz' : IsZero (E.obj S.homology) :=
    IsZero.of_iso hz (S.mapHomologyIso E).symm
  exact (IsZero.iff_id_eq_zero (E.obj S.homology)).mp hz'

end CategoryTheory.ShortComplex

universe w

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]
    {F G H : C ⥤ AddCommGrpCat.{w}}

/-- Pointwise exactness and surjectivity identify an abelian presheaf
with the categorical cokernel, using the shared evaluation criterion. -/
def presheafCokernelIsoOfExact (f : F ⟶ G) (g : G ⟶ H) (wfg : f ≫ g = 0)
    (hex : ∀ X : C, ∀ y, g.app X y = 0 → ∃ x, f.app X x = y)
    (hsurj : ∀ X : C, Function.Surjective (g.app X)) :
    cokernel f ≅ H := by
  let S := ShortComplex.mk f g wfg
  have hS : S.Exact := by
    apply ShortComplex.exact_of_evaluation
    intro X
    exact (ShortComplex.ab_exact_iff _).mpr (hex X)
  have : Epi g := by
    rw [NatTrans.epi_iff_epi_app]
    intro X
    exact (AddCommGrpCat.epi_iff_surjective (g.app X)).mpr (hsurj X)
  exact (cokernelIsCokernel f).coconePointUniqueUpToIso hS.gIsCokernel

end CategoryTheory

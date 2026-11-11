/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.GaloisSections
public import Nyll.SchemeTheory.FiniteEtale.Forget.Extensive
public import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveSheaves
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Nyll.EtaleFundamentalGroups.GaloisCovers.SelfProduct

/-!
# Actual sheaf sections on finite etale coproducts

The restriction of any small-etale sheaf to finite etale schemes sends
finite disjoint coproducts to products. This supplies arbitrary coefficient
sections on the deck-graph decomposition of a Galois cover's self-product.
No local-constancy or finiteness assumption on the coefficient sheaf is used.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry

namespace EtaleCohomology

/-- The actual small-etale sheaf condition supplies preservation of finite
products after restriction to the opposite finite-etale category. -/
theorem finiteEtaleSheaf_preservesFiniteProducts
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology (Type u)) :
    PreservesFiniteProducts ((finiteEtaleInclusion X).op ⋙ F.obj) := by
  let I : FiniteEtale X ⥤ X.Etale := finiteEtaleInclusion X
  let T : FiniteEtale X ⥤ Type u :=
    FiniteEtale.forget X ⋙ Over.forget X ⋙ Scheme.forgetToTop ⋙ forget TopCat
  rw [← Presieve.isSheaf_iff_preservesFiniteProducts]
  rw [extensiveTopology, Presieve.isSheaf_coverage]
  intro Z R hR
  obtain ⟨ι, hι, A, π, rfl, hiso⟩ := hR
  have : IsIso (Sigma.desc π) := hiso
  let c : Cofan A := Cofan.mk Z π
  have : IsIso (Sigma.desc c.inj) := by
    change IsIso (Sigma.desc π)
    exact hiso
  have hc : IsColimit c := Cofan.isColimitOfIsIsoSigmaDesc c
  let j : ∀ i, I.obj (A i) ⟶ I.obj Z := fun i => I.map (π i)
  have hcover : Sieve.ofArrows (fun i => I.obj (A i)) j ∈
      X.smallEtaleTopology (I.obj Z) := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff j).mpr
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, a, ha⟩ :=
      Types.jointly_surjective_of_isColimit (isColimitOfPreserves T hc) x
    exact Set.mem_iUnion.mpr ⟨i.as, a, ha⟩
  have : (Presieve.ofArrows A π).HasPairwisePullbacks := inferInstance
  have : I.PreservesPairwisePullbacks (Presieve.ofArrows A π) := inferInstance
  rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks,
    Presieve.map_ofArrows]
  apply (Presieve.isSheafFor_iff_generate _).mpr
  exact (isSheaf_iff_isSheaf_of_type _ _).mp F.property _ hcover

/-- Sections on a finite disjoint coproduct are arbitrary families of sections
on the actual summands. -/
def finiteEtaleSheafCoproductSectionsEquiv
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology (Type u))
    {ι : Type u} [Finite ι] (A : ι → FiniteEtale X) :
    F.obj.obj (op ((finiteEtaleInclusion X).obj (∐ A))) ≃
      (∀ i, F.obj.obj (op ((finiteEtaleInclusion X).obj (A i)))) := by
  let H : (FiniteEtale X)ᵒᵖ ⥤ Type u :=
    (finiteEtaleInclusion X).op ⋙ F.obj
  have : PreservesFiniteProducts H := finiteEtaleSheaf_preservesFiniteProducts X F
  exact (H.mapIso (opCoproductIsoProduct A) ≪≫
    PreservesProduct.iso H (fun i => op (A i)) ≪≫
    Types.productIso (fun i => H.obj (op (A i)))).toEquiv

/-- The coproduct section equivalence evaluates by restriction to a summand. -/
theorem finiteEtaleSheafCoproductSectionsEquiv_apply
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology (Type u))
    {ι : Type u} [Finite ι] (A : ι → FiniteEtale X)
    (s : F.obj.obj (op ((finiteEtaleInclusion X).obj (∐ A)))) (i : ι) :
    finiteEtaleSheafCoproductSectionsEquiv X F A s i =
      F.obj.map ((finiteEtaleInclusion X).map (Sigma.ι A i)).op s := by
  let H : (FiniteEtale X)ᵒᵖ ⥤ Type u :=
    (finiteEtaleInclusion X).op ⋙ F.obj
  have : PreservesFiniteProducts H := finiteEtaleSheaf_preservesFiniteProducts X F
  change (Types.productIso (fun i => H.obj (op (A i)))).hom
    ((PreservesProduct.iso H (fun i => op (A i))).hom
      (H.map (opCoproductIsoProduct A).hom s)) i = H.map (Sigma.ι A i).op s
  rw [Types.productIso_hom_comp_eval_apply, PreservesProduct.iso_hom]
  change (piComparison H (fun i => op (A i)) ≫ Pi.π _ i)
    (H.map (opCoproductIsoProduct A).hom s) = _
  rw [piComparison_comp_π]
  rw [← ConcreteCategory.comp_apply, ← H.map_comp,
    opCoproductIsoProduct_hom_comp_π]

/-- Sections on the self-product of an actual Galois cover are functions on
its actual deck group with values in sections on the cover. -/
def galoisSelfProductSectionsEquiv
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology (Type u))
    (Y : FiniteEtale X) [CategoryTheory.PreGaloisCategory.IsGalois Y] :
    F.obj.obj (op ((finiteEtaleInclusion X).obj (Y ⨯ Y))) ≃
      (Aut Y → F.obj.obj (op ((finiteEtaleInclusion X).obj Y))) :=
  (F.obj.mapIso ((finiteEtaleInclusion X).mapIso
    (CategoryTheory.PreGaloisCategory.galoisSelfProductIso Y)).op).toEquiv.trans
      (finiteEtaleSheafCoproductSectionsEquiv X F (fun _ : Aut Y => Y))

/-- The deck coordinate is restriction along the actual deck graph. -/
theorem galoisSelfProductSectionsEquiv_apply
    (X : Scheme.{u}) [ConnectedSpace X]
    (F : Sheaf X.smallEtaleTopology (Type u))
    (Y : FiniteEtale X) [CategoryTheory.PreGaloisCategory.IsGalois Y]
    (s : F.obj.obj (op ((finiteEtaleInclusion X).obj (Y ⨯ Y)))) (σ : Aut Y) :
    galoisSelfProductSectionsEquiv X F Y s σ =
      F.obj.map ((finiteEtaleInclusion X).map (prod.lift (𝟙 Y) σ.asIso.hom)).op s := by
  rw [galoisSelfProductSectionsEquiv, Equiv.trans_apply,
    finiteEtaleSheafCoproductSectionsEquiv_apply]
  change F.obj.map ((finiteEtaleInclusion X).map (Sigma.ι (fun _ : Aut Y => Y) σ)).op
    (F.obj.map ((finiteEtaleInclusion X).map
      (CategoryTheory.PreGaloisCategory.galoisSelfProductIso Y).hom).op s) = _
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp,
    ← Functor.map_comp, CategoryTheory.PreGaloisCategory.galoisSelfProductIso_ι]

end EtaleCohomology

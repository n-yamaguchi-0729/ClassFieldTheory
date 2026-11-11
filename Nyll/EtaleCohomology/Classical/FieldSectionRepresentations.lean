/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FieldGaloisAction
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Representations on actual etale field sections

The previously proved actual field action is bundled as an integer-linear
representation. Unit sections are equivariantly identified with the existing
representation on field units, so its group-cohomology theorems apply
without an assumed action comparison.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.FiniteEtale

namespace EtaleCohomology

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- Integer-linear representation on actual sheaf sections over the
finite Galois field extension. -/
def fieldGaloisSheafSectionsRep
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    Rep.{u} ℤ Gal(L/K) :=
  Rep.of
    { toFun := fun σ => ((fieldGaloisSheafAction K L F σ).asIso.hom).hom.toIntLinearMap
      map_one' := by
        apply LinearMap.ext
        intro s
        change (fieldGaloisSheafAction K L F 1).asIso.hom s = s
        rw [map_one]
        rfl
      map_mul' σ τ := by
        apply LinearMap.ext
        intro s
        exact congrArg (fun a => a.asIso.hom s) (map_mul (fieldGaloisSheafAction K L F) σ τ) }

/-- Actual coefficient morphisms induce equivariant maps of field-section
representations. -/
def fieldGaloisSheafSectionsRepMap
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}}
    (η : F ⟶ G) :
    fieldGaloisSheafSectionsRep K L F ⟶ fieldGaloisSheafSectionsRep K L G :=
  Rep.ofHom
    ⟨(η.hom.app (op ((finiteEtaleInclusion (Spec (.of K))).obj
      (FiniteEtale.mk (ξ K L))))).hom.toIntLinearMap, fun σ => by
        apply LinearMap.ext
        intro s
        exact ConcreteCategory.congr_hom (C := AddCommGrpCat.{u})
          (fieldGaloisSheafAction_naturality K L η σ) s⟩

/-- The actual section representation is functorial in the coefficient sheaf. -/
def fieldGaloisSheafSectionsFunctor :
    Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} ⥤ Rep.{u} ℤ Gal(L/K) where
  obj := fieldGaloisSheafSectionsRep K L
  map := fieldGaloisSheafSectionsRepMap K L
  map_id F := by
    ext s
    rfl
  map_comp η θ := by
    ext s
    rfl

/-- The actual field-section representation functor is additive. -/
instance fieldGaloisSheafSectionsFunctor_additive :
    (fieldGaloisSheafSectionsFunctor K L).Additive where
  map_add := by
    intro F G η θ
    ext s
    rfl

/-- Actual unit sections have the existing usual field-unit representation.
The intertwining law is the previously proved geometric pullback identity. -/
def fieldGaloisSheafSectionsUnitsIso :
    fieldGaloisSheafSectionsRep K L (etaleMultiplicativeGroupSheaf (Spec (.of K))) ≅
      Rep.ofAlgebraAutOnUnits K L :=
  Rep.mkIso (Representation.Equiv.mk
    (etaleMultiplicativeGroupSpecSectionsEquiv (Spec (.of K)) (.of L)
      (ξ K L)).toIntLinearEquiv (fun σ => by
        apply LinearMap.ext
        intro s
        exact fieldGaloisSheafAction_units K L σ s))

end EtaleCohomology

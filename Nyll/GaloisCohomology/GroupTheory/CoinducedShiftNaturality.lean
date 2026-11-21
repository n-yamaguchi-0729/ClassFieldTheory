/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.GroupTheory.CoinducedShift
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Functoriality of the actual coinduced shift

Coefficient maps act on coinduced functions by postcomposition. The resulting
commuting square induces the map of actual cokernels and the map of the
dimension-shifting short exact sequences.
-/

@[expose] public section

noncomputable section

universe u uR

open CategoryTheory CategoryTheory.Limits

namespace Rep

variable {R : Type uR} {G : Type u} [CommRing R] [Group G]

/-- The middle term of the shifting sequence, with its actual action on maps. -/
def coindShiftMiddleFunctor : Rep.{u} R G ⥤ Rep.{u} R G :=
  resFunctor (⊥ : Subgroup G).subtype ⋙ coindFunctor R (⊥ : Subgroup G).subtype

/-- A coefficient map is applied pointwise to the coinduced functions. -/
theorem coindShiftMiddleFunctor_map_apply {A B : Rep.{u} R G} (f : A ⟶ B)
    (x : (coindShiftMiddleFunctor (R := R) (G := G)).obj A) (g : G) :
    (((coindShiftMiddleFunctor (R := R) (G := G)).map f).hom x).1 g =
      f.hom (x.1 g) := rfl

/-- The coinduction embedding commutes with the original coefficient map. -/
theorem coindShiftUnit_naturality {A B : Rep.{u} R G} (f : A ⟶ B) :
    coindShiftUnit A ≫ (coindShiftMiddleFunctor (R := R) (G := G)).map f =
      f ≫ coindShiftUnit B := by
  apply Rep.hom_ext
  apply DFunLike.ext
  intro a
  apply Subtype.ext
  funext g
  exact hom_comm_apply f g a

/-- The shift map is the induced map of the actual cokernels. -/
def coindShiftUpMap {A B : Rep.{u} R G} (f : A ⟶ B) :
    coindShiftUp A ⟶ coindShiftUp B :=
  cokernel.map (coindShiftUnit A) (coindShiftUnit B) f
    ((coindShiftMiddleFunctor (R := R) (G := G)).map f) (coindShiftUnit_naturality f)

/-- Its defining square uses the original cokernel projections. -/
theorem coindShiftUpMap_π {A B : Rep.{u} R G} (f : A ⟶ B) :
    cokernel.π (coindShiftUnit A) ≫ coindShiftUpMap f =
      (coindShiftMiddleFunctor (R := R) (G := G)).map f ≫
        cokernel.π (coindShiftUnit B) :=
  cokernel.π_desc _ _ _

/-- The induced cokernel map preserves identity morphisms. -/
theorem coindShiftUpMap_id (A : Rep.{u} R G) :
    coindShiftUpMap (𝟙 A) = 𝟙 (coindShiftUp A) := by
  let F := coindShiftMiddleFunctor (R := R) (G := G)
  let p : F.obj A ⟶ coindShiftUp A := cokernel.π (coindShiftUnit A)
  let : Epi p := (inferInstance : Epi (cokernel.π (coindShiftUnit A)))
  apply (cancel_epi p).mp
  have hp : p ≫ coindShiftUpMap (𝟙 A) = F.map (𝟙 A) ≫ p := coindShiftUpMap_π _
  rw [hp, F.map_id, Category.id_comp, Category.comp_id]

/-- The induced cokernel map preserves composition. -/
theorem coindShiftUpMap_comp {A B C : Rep.{u} R G} (f : A ⟶ B) (g : B ⟶ C) :
    coindShiftUpMap (f ≫ g) = coindShiftUpMap f ≫ coindShiftUpMap g := by
  let F := coindShiftMiddleFunctor (R := R) (G := G)
  let p (X : Rep.{u} R G) : F.obj X ⟶ coindShiftUp X := cokernel.π (coindShiftUnit X)
  let : Epi (p A) := (inferInstance : Epi (cokernel.π (coindShiftUnit A)))
  apply (cancel_epi (p A)).mp
  have hp {X Y : Rep.{u} R G} (h : X ⟶ Y) :
      p X ≫ coindShiftUpMap h = F.map h ≫ p Y := coindShiftUpMap_π h
  rw [hp (f ≫ g), ← Category.assoc, hp f, Category.assoc, hp g,
    ← Category.assoc, F.map_comp]

/-- The upward shift is a functor on the original category of representations. -/
def coindShiftUpFunctor : Rep.{u} R G ⥤ Rep.{u} R G where
  obj := coindShiftUp
  map := coindShiftUpMap
  map_id := coindShiftUpMap_id
  map_comp := coindShiftUpMap_comp

/-- The actual coefficient map, pointwise map, and cokernel map form a map
of the dimension-shifting short exact sequences. -/
def coindShiftSequenceMap {A B : Rep.{u} R G} (f : A ⟶ B) :
    coindShiftSequence A ⟶ coindShiftSequence B where
  τ₁ := f
  τ₂ := (coindShiftMiddleFunctor (R := R) (G := G)).map f
  τ₃ := coindShiftUpMap f
  comm₁₂ := (coindShiftUnit_naturality f).symm
  comm₂₃ := (coindShiftUpMap_π f).symm

end Rep

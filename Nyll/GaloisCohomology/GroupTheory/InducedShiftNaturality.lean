/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.GroupTheory.InducedShift
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Functoriality of the actual induced shift

Naturality of the induction-restriction counit supplies the commuting square.
The corresponding map of actual kernels preserves identities and compositions
and gives a map of the specified short exact sequences.
-/

@[expose] public section

noncomputable section

universe u uR

open CategoryTheory CategoryTheory.Limits

namespace Rep

variable {R : Type uR} {G : Type u} [CommRing R] [Group G]

/-- The actual induced middle term, with the standard induced maps. -/
def indShiftMiddleFunctor : Rep.{max u uR} R G ⥤ Rep.{max u uR} R G :=
  resFunctor (⊥ : Subgroup G).subtype ⋙ indFunctor R (⊥ : Subgroup G).subtype

/-- The original induction counit commutes with coefficient morphisms. -/
theorem indShiftCounit_naturality {A B : Rep.{max u uR} R G} (f : A ⟶ B) :
    (indShiftMiddleFunctor (R := R) (G := G)).map f ≫ indShiftCounit B =
      indShiftCounit A ≫ f :=
  (indResAdjunction.{max u uR} R (⊥ : Subgroup G).subtype).counit.naturality f

/-- The downward shift map is the induced map of the actual kernels. -/
def indShiftDownMap {A B : Rep.{max u uR} R G} (f : A ⟶ B) :
    indShiftDown A ⟶ indShiftDown B :=
  kernel.map (indShiftCounit A) (indShiftCounit B)
    ((indShiftMiddleFunctor (R := R) (G := G)).map f) f
    (indShiftCounit_naturality f).symm

/-- The induced kernel map has the specified square with the kernel inclusions. -/
theorem indShiftDownMap_ι {A B : Rep.{max u uR} R G} (f : A ⟶ B) :
    indShiftDownMap f ≫ kernel.ι (indShiftCounit B) =
      kernel.ι (indShiftCounit A) ≫ (indShiftMiddleFunctor (R := R) (G := G)).map f :=
  kernel.lift_ι _ _ _

/-- The actual kernel map preserves identity morphisms. -/
theorem indShiftDownMap_id (A : Rep.{max u uR} R G) :
    indShiftDownMap (𝟙 A) = 𝟙 (indShiftDown A) := by
  let F := indShiftMiddleFunctor (R := R) (G := G)
  let i : indShiftDown A ⟶ F.obj A := kernel.ι (indShiftCounit A)
  let : Mono i := (inferInstance : Mono (kernel.ι (indShiftCounit A)))
  apply (cancel_mono i).mp
  have hi : indShiftDownMap (𝟙 A) ≫ i = i ≫ F.map (𝟙 A) := indShiftDownMap_ι _
  rw [hi, F.map_id, Category.comp_id, Category.id_comp]

/-- The actual kernel map preserves composition. -/
theorem indShiftDownMap_comp {A B C : Rep.{max u uR} R G} (f : A ⟶ B) (g : B ⟶ C) :
    indShiftDownMap (f ≫ g) = indShiftDownMap f ≫ indShiftDownMap g := by
  let F := indShiftMiddleFunctor (R := R) (G := G)
  let i (X : Rep.{max u uR} R G) : indShiftDown X ⟶ F.obj X := kernel.ι (indShiftCounit X)
  let : Mono (i C) := (inferInstance : Mono (kernel.ι (indShiftCounit C)))
  apply (cancel_mono (i C)).mp
  have hi {X Y : Rep.{max u uR} R G} (h : X ⟶ Y) :
      indShiftDownMap h ≫ i Y = i X ≫ F.map h := indShiftDownMap_ι h
  rw [hi (f ≫ g), Category.assoc, hi g, ← Category.assoc, hi f,
    Category.assoc, F.map_comp]

/-- The actual kernel construction defines the downward shift functor. -/
def indShiftDownFunctor : Rep.{max u uR} R G ⥤ Rep.{max u uR} R G where
  obj := indShiftDown
  map := indShiftDownMap
  map_id := indShiftDownMap_id
  map_comp := indShiftDownMap_comp

/-- A coefficient morphism gives a map of the actual induced shifting sequences. -/
def indShiftSequenceMap {A B : Rep.{max u uR} R G} (f : A ⟶ B) :
    indShiftSequence A ⟶ indShiftSequence B where
  τ₁ := indShiftDownMap f
  τ₂ := (indShiftMiddleFunctor (R := R) (G := G)).map f
  τ₃ := f
  comm₁₂ := indShiftDownMap_ι f
  comm₂₃ := indShiftCounit_naturality f

end Rep

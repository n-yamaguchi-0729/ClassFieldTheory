/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.FieldFiniteCover
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# The actual finite Galois section diagram

Finite Galois subfields of the algebraic closure index actual etale
objects. Transition maps are the literal field inclusions on spectra,
and the section diagram uses actual sheaf restriction.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry

namespace EtaleCohomology

variable (K : Type u) [Field K]

/-- The actual inverse diagram of finite Galois spectra over a field. -/
def finiteGaloisEtaleDiagram :
    (FiniteGaloisIntermediateField K (AlgebraicClosure K))ᵒᵖ ⥤
      (Spec (.of K)).Etale where
  obj E := finiteGaloisEtaleObject K E.unop
  map {E L} h := MorphismProperty.Over.homMk
    (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h.unop.le).toRingHom))
    (by
      change Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h.unop.le).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K L.unop)) =
        Spec.map (CommRingCat.ofHom (algebraMap K E.unop))
      rw [← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      exact (IntermediateField.inclusion h.unop.le).commutes x)
  map_id E := by
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom
      (IntermediateField.inclusion (le_refl E.unop.toIntermediateField)).toRingHom) = 𝟙 _
    rw [← Spec.map_id]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    rfl
  map_comp h g := by
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom
        (IntermediateField.inclusion (g.unop.le.trans h.unop.le)).toRingHom) =
      Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h.unop.le).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (IntermediateField.inclusion g.unop.le).toRingHom)
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    rfl

/-- Actual sheaf sections over finite Galois subfields, with geometric
restriction along their canonical inclusions. -/
def finiteGaloisSectionDiagram
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    FiniteGaloisIntermediateField K (AlgebraicClosure K) ⥤ AddCommGrpCat.{u} :=
  (finiteGaloisEtaleDiagram K).rightOp ⋙ F.obj

/-- The actual direct limit of sections over finite Galois subfields. -/
def finiteGaloisSectionColimit
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :
    AddCommGrpCat.{u} :=
  colimit (finiteGaloisSectionDiagram K F)

/-- An actual section at a finite Galois stage maps to the section colimit. -/
def finiteGaloisSectionColimitι
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    F.obj.obj (op (finiteGaloisEtaleObject K E)) ⟶ finiteGaloisSectionColimit K F :=
  colimit.ι (finiteGaloisSectionDiagram K F) E

/-- Canonical field inclusions induce the defining transition relations
in the actual section colimit. -/
theorem finiteGaloisSectionColimitι_transition
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    {E L : FiniteGaloisIntermediateField K (AlgebraicClosure K)} (h : E ⟶ L) :
    F.obj.map ((finiteGaloisEtaleDiagram K).map h.op).op ≫
      finiteGaloisSectionColimitι K F L =
        finiteGaloisSectionColimitι K F E :=
  colimit.w (finiteGaloisSectionDiagram K F) h

/-- Every element of the actual section colimit is represented over one
finite Galois extension. -/
theorem finiteGaloisSectionColimit_exists_stage
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (x : finiteGaloisSectionColimit K F) :
    ∃ (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))
      (s : F.obj.obj (op (finiteGaloisEtaleObject K E))),
      finiteGaloisSectionColimitι K F E s = x :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget AddCommGrpCat.{u})
      (colimit.isColimit (finiteGaloisSectionDiagram K F))) x

/-- Equality of actual section-colimit elements is witnessed by restriction
to a common finite Galois extension. -/
theorem finiteGaloisSectionColimit_eq_iff
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    {E L : FiniteGaloisIntermediateField K (AlgebraicClosure K)}
    (s : F.obj.obj (op (finiteGaloisEtaleObject K E)))
    (t : F.obj.obj (op (finiteGaloisEtaleObject K L))) :
    finiteGaloisSectionColimitι K F E s = finiteGaloisSectionColimitι K F L t ↔
      ∃ (M : FiniteGaloisIntermediateField K (AlgebraicClosure K))
        (h : E ⟶ M) (g : L ⟶ M),
        F.obj.map ((finiteGaloisEtaleDiagram K).map h.op).op s =
          F.obj.map ((finiteGaloisEtaleDiagram K).map g.op).op t :=
  Types.FilteredColimit.isColimit_eq_iff
    (finiteGaloisSectionDiagram K F ⋙ forget AddCommGrpCat.{u})
    (isColimitOfPreserves (forget AddCommGrpCat.{u})
      (colimit.isColimit (finiteGaloisSectionDiagram K F)))

/-- A finite collection of colimit sections has representatives in a single
actual finite Galois extension. -/
theorem finiteGaloisSectionColimit_exists_common_stage
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    {ι : Type*} [Finite ι] (x : ι → finiteGaloisSectionColimit K F) :
    ∃ (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))
      (s : ι → F.obj.obj (op (finiteGaloisEtaleObject K E))),
      ∀ i, finiteGaloisSectionColimitι K F E (s i) = x i := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  choose E s hs using fun i => finiteGaloisSectionColimit_exists_stage K F (x i)
  obtain ⟨M, hM⟩ := IsFiltered.sup_objs_exists (Finset.univ.image E)
  let h (i : ι) : E i ⟶ M :=
    (hM (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)).some
  refine ⟨M, fun i => (finiteGaloisSectionDiagram K F).map (h i) (s i), ?_⟩
  intro i
  exact (ConcreteCategory.congr_hom
    (finiteGaloisSectionColimitι_transition K F (h i)) (s i)).trans (hs i)

end EtaleCohomology

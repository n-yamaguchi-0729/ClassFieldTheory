/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.ConstantPresentation
public import Nyll.SchemeTheory.Etale.OverField.Decomposition
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.SeparableClosure
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic

/-!
# Finite étale refinements over a field

Every covering sieve of the terminal object of the small étale site of a
field contains a connected finite étale surjective cover. We select an
actual spectrum of a finite separable field from the established geometric
decomposition of an étale neighborhood.

Consequently an epimorphism of abelian sheaves admits a lift of any given
global section after an actual connected finite étale cover. This is the
local lifting input for comparing field étale cohomology with finite
Galois stages; no cohomology comparison is assumed.
-/

@[expose] public section

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- An arbitrary étale covering sieve over a field has a connected finite
étale surjective refinement. -/
theorem exists_finiteEtale_mem_covering_sieve_of_field
    (K : Type u) [Field K]
    (S : Sieve (Scheme.Etale.mk (𝟙 (Spec (.of K)))))
    (hS : S ∈ (Spec (.of K)).smallEtaleTopology _) :
    ∃ (V : (Spec (.of K)).Etale)
      (f : V ⟶ Scheme.Etale.mk (𝟙 (Spec (.of K)))),
      IsFinite V.hom ∧ ConnectedSpace V.left ∧
        Function.Surjective V.hom ∧ S f := by
  obtain ⟨Y, g, y, hg, _⟩ := exists_etale_neighborhood_in_sieve S hS
    (default : Spec (.of K))
  obtain ⟨L, a, e, hfield, hsep, he⟩ := Scheme.Etale.exists_iso_sigmaSpec K Y
  let : Field (L y) := (hfield y).toField
  let : Algebra K (L y) := (a y).hom.toAlgebra
  have : Module.Finite K (L y) := (hsep y).1
  have : Algebra.IsSeparable K (L y) := (hsep y).2
  have : Algebra.FormallyEtale K (L y) := Algebra.FormallyEtale.of_isSeparable K (L y)
  have : Algebra.Etale K (L y) :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  have hf : IsFiniteEtale (Spec.map (a y)) := by
    rw [IsFiniteEtale.SpecMap_iff]
    change (algebraMap K (L y)).FiniteEtale
    rw [RingHom.finiteEtale_algebraMap_iff, Algebra.finiteEtale_iff]
    exact ⟨inferInstance, inferInstance⟩
  have : Etale (Spec.map (a y)) := hf.toEtale
  let V : (Spec (.of K)).Etale := Scheme.Etale.mk (Spec.map (a y))
  let l : V ⟶ Y := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @AlgebraicGeometry.Etale)
    (Q := ⊤)
    (Sigma.ι (fun z => Spec (L z)) y ≫ e.hom) (by
      change (Sigma.ι (fun z => Spec (L z)) y ≫ e.hom) ≫ Y.hom = Spec.map (a y)
      rw [Category.assoc, he, Sigma.ι_comp_desc])
  refine ⟨V, l ≫ g, hf.toIsFinite, ?_, ?_, S.downward_closed hg l⟩
  · change ConnectedSpace (Spec (L y))
    infer_instance
  · change Function.Surjective (Spec.map (a y))
    intro x
    let z : PrimeSpectrum (L y) := ⟨⊥, inferInstance⟩
    refine ⟨z, ?_⟩
    exact Subsingleton.elim (Spec.map (a y) z) x

/-- A global section of an abelian sheaf locally lifts through an
epimorphism on an actual connected finite étale cover of the field. -/
theorem exists_finiteEtale_lift_sheaf_epi_section_of_field
    (K : Type u) [Field K]
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}}
    (η : F ⟶ G) [Epi η]
    (t : G.obj.obj (op (Scheme.Etale.mk (𝟙 (Spec (.of K)))))) :
    ∃ (V : (Spec (.of K)).Etale)
      (f : V ⟶ Scheme.Etale.mk (𝟙 (Spec (.of K)))),
      IsFinite V.hom ∧ ConnectedSpace V.left ∧ Function.Surjective V.hom ∧
        ∃ s : F.obj.obj (op V), η.hom.app (op V) s = G.obj.map f.op t := by
  have : Sheaf.IsLocallySurjective η :=
    (Sheaf.isLocallySurjective_iff_epi'
      (J := (Spec (.of K)).smallEtaleTopology) AddCommGrpCat.{u} η).mpr inferInstance
  obtain ⟨V, f, hf, hc, hs, hmem⟩ :=
    exists_finiteEtale_mem_covering_sieve_of_field K (Presheaf.imageSieve η.hom t)
      (Presheaf.imageSieve_mem (Spec (.of K)).smallEtaleTopology η.hom t)
  exact ⟨V, f, hf, hc, hs, hmem⟩

/-- The actual spectrum of a finite Galois intermediate field, as an object
of the small étale site. -/
def finiteGaloisEtaleObject (K : Type u) [Field K]
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    (Spec (.of K)).Etale := by
  have : Algebra.FormallyEtale K E := Algebra.FormallyEtale.of_isSeparable K E
  have : Algebra.Etale K E :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  have h : IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap K E))) := by
    rw [IsFiniteEtale.SpecMap_iff]
    change (algebraMap K E).FiniteEtale
    rw [RingHom.finiteEtale_algebraMap_iff, Algebra.finiteEtale_iff]
    exact ⟨inferInstance, inferInstance⟩
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap K E))) := h.toEtale
  exact Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap K E)))

/-- A covering sieve of any pointed étale object over a field
has an actual finite Galois refinement over the original base field. -/
theorem exists_finiteGalois_mem_covering_sieve_of_field_object
    (K : Type u) [Field K]
    (V : (Spec (.of K)).Etale) (x : V.left)
    (S : Sieve V)
    (hS : S ∈ (Spec (.of K)).smallEtaleTopology _) :
    ∃ (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))
      (f : finiteGaloisEtaleObject K E ⟶ V),
      S f := by
  obtain ⟨Y, g, y, hg, _⟩ := exists_etale_neighborhood_in_sieve S hS
    x
  obtain ⟨L, a, e, hfield, hsep, he⟩ := Scheme.Etale.exists_iso_sigmaSpec K Y
  let : Field (L y) := (hfield y).toField
  let : Algebra K (L y) := (a y).hom.toAlgebra
  have : Module.Finite K (L y) := (hsep y).1
  have : Algebra.IsSeparable K (L y) := (hsep y).2
  have : Algebra.IsSeparable K
      (IntermediateField.normalClosure K (L y) (AlgebraicClosure K)) := by
    rw [normalClosure_def]
    have : ∀ b : L y →ₐ[K] AlgebraicClosure K, Algebra.IsSeparable K b.fieldRange :=
      fun b => AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField b)
    exact IntermediateField.isSeparable_iSup K (AlgebraicClosure K)
  let E : FiniteGaloisIntermediateField K (AlgebraicClosure K) :=
    { toIntermediateField := IntermediateField.normalClosure K (L y) (AlgebraicClosure K)
      finiteDimensional := inferInstance
      isGalois := ⟨⟩ }
  let b : L y →ₐ[K] E :=
    (normalClosure.algHomEquiv K (L y) (AlgebraicClosure K)).symm
      IsAlgClosed.lift
  let l : finiteGaloisEtaleObject K E ⟶ Y := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @AlgebraicGeometry.Etale) (Q := ⊤)
    (Spec.map (CommRingCat.ofHom b.toRingHom) ≫
      Sigma.ι (fun z => Spec (L z)) y ≫ e.hom) (by
        change (Spec.map (CommRingCat.ofHom b.toRingHom) ≫
          Sigma.ι (fun z => Spec (L z)) y ≫ e.hom) ≫ Y.hom =
            Spec.map (CommRingCat.ofHom (algebraMap K E))
        rw [Category.assoc, Category.assoc, he, Sigma.ι_comp_desc]
        rw [← Spec.map_comp]
        congr 1
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro k
        exact b.commutes k)
  exact ⟨E, l ≫ g, S.downward_closed hg l⟩

/-- A cover of any base field can be refined
inside its algebraic closure by an actual finite Galois extension. -/
theorem exists_finiteGalois_mem_covering_sieve_of_field
    (K : Type u) [Field K]
    (S : Sieve (Scheme.Etale.mk (𝟙 (Spec (.of K)))))
    (hS : S ∈ (Spec (.of K)).smallEtaleTopology _) :
    ∃ (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))
      (f : finiteGaloisEtaleObject K E ⟶ Scheme.Etale.mk (𝟙 (Spec (.of K)))),
      S f :=
  exists_finiteGalois_mem_covering_sieve_of_field_object K
    (Scheme.Etale.mk (𝟙 (Spec (.of K)))) (default : Spec (.of K)) S hS

/-- A finite family of actual sections lifts simultaneously through a
sheaf epimorphism after a single actual finite Galois refinement. -/
theorem exists_finiteGalois_lift_finite_sections_of_field
    (K : Type u) [Field K]
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}}
    (η : F ⟶ G) [Epi η]
    (V : (Spec (.of K)).Etale) (x : V.left)
    {ι : Type*} [Finite ι] (t : ι → G.obj.obj (op V)) :
    ∃ (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))
      (f : finiteGaloisEtaleObject K E ⟶ V),
      ∀ i, ∃ s : F.obj.obj (op (finiteGaloisEtaleObject K E)),
        η.hom.app _ s = G.obj.map f.op (t i) := by
  have : Fintype ι := Fintype.ofFinite ι
  have : Sheaf.IsLocallySurjective η :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} η).mpr inferInstance
  let J := (Spec (.of K)).smallEtaleTopology
  let Sᵢ (i : ι) : J.Cover V :=
    ⟨Presheaf.imageSieve η.hom (t i), Presheaf.imageSieve_mem J η.hom (t i)⟩
  let S : J.Cover V := Finset.univ.inf Sᵢ
  obtain ⟨E, f, hf⟩ :=
    exists_finiteGalois_mem_covering_sieve_of_field_object K V x S S.condition
  refine ⟨E, f, ?_⟩
  intro i
  have hi : S ≤ Sᵢ i := Finset.inf_le (Finset.mem_univ i)
  exact hi f hf

end EtaleCohomology

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FiniteGaloisSectionColimit
public import Mathlib.FieldTheory.Normal.Basic

/-!
# Canonical finite Galois refinements

An arbitrary morphism between finite Galois spectra can be corrected by a
source automorphism to the canonical inclusion. Thus local sheaf lifting
really occurs in the canonical filtered diagram, not just after an
unrelated embedding.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry

namespace EtaleCohomology

variable (K : Type u) [Field K]

private theorem normalSubfield_embedding_factors
    (E L : FiniteGaloisIntermediateField K (AlgebraicClosure K))
    (a : E →ₐ[K] L) :
    ∃ (h : E ≤ L) (σ : Gal(L/K)),
      ∀ x : E, σ (IntermediateField.inclusion h x) = a x := by
  have hr : (L.toIntermediateField.val.comp a).fieldRange = E.toIntermediateField :=
    AlgHom.fieldRange_of_normal _
  have h : E ≤ L := by
    intro x hx
    have hx' : x ∈ (L.toIntermediateField.val.comp a).fieldRange := hr.symm ▸ hx
    obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.mp hx'
    rw [← hy]
    exact (a y).property
  let : Algebra E L := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower K E L :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      ((IntermediateField.inclusion h).commutes x).symm)
  let b : L →ₐ[K] L := a.liftNormal L
  let σ : Gal(L/K) := AlgEquiv.ofBijective b (AlgHom.normal_bijective K L L b)
  refine ⟨h, σ, ?_⟩
  intro x
  exact a.liftNormal_commutes L x

/-- An arbitrary actual map of finite Galois spectra can be precomposed
with a source automorphism to become the canonical inclusion map. -/
theorem finiteGaloisEtaleHom_correct_to_canonical
    (E L : FiniteGaloisIntermediateField K (AlgebraicClosure K))
    (f : finiteGaloisEtaleObject K L ⟶ finiteGaloisEtaleObject K E) :
    ∃ (h : E ⟶ L)
      (t : finiteGaloisEtaleObject K L ⟶ finiteGaloisEtaleObject K L),
      t ≫ f = (finiteGaloisEtaleDiagram K).map h.op := by
  let f₀ : Spec (.of L) ⟶ Spec (.of E) := f.left
  let a₀ : CommRingCat.of E ⟶ CommRingCat.of L := Spec.preimage f₀
  have hpre : Spec.map a₀ = f₀ := Spec.map_preimage f₀
  have hc : CommRingCat.ofHom (algebraMap K E) ≫ a₀ =
      CommRingCat.ofHom (algebraMap K L) := by
    apply Spec.map_injective
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap K E)) a₀).trans
      ((congrArg (fun g : Spec (.of L) ⟶ Spec (.of E) =>
        g ≫ Spec.map (CommRingCat.ofHom (algebraMap K E))) hpre).trans f.w)
  let a : E →ₐ[K] L :=
    { toRingHom := a₀.hom
      commutes' := fun x => ConcreteCategory.congr_hom hc x }
  obtain ⟨h, σ, hσ⟩ := normalSubfield_embedding_factors K E L a
  let t : finiteGaloisEtaleObject K L ⟶ finiteGaloisEtaleObject K L :=
    MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom σ.symm.toRingHom)) (by
      change Spec.map (CommRingCat.ofHom σ.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) =
          Spec.map (CommRingCat.ofHom (algebraMap K L))
      rw [← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      exact σ.symm.commutes x)
  refine ⟨homOfLE h, t, ?_⟩
  apply MorphismProperty.Over.Hom.ext
  change Spec.map (CommRingCat.ofHom σ.symm.toRingHom) ≫ f₀ =
    Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom)
  have hab : a₀ ≫ CommRingCat.ofHom σ.symm.toRingHom =
      CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change σ.symm (a x) = IntermediateField.inclusion h x
    rw [← hσ x, σ.symm_apply_apply]
  have h₁ : Spec.map (CommRingCat.ofHom σ.symm.toRingHom) ≫ f₀ =
      Spec.map (CommRingCat.ofHom σ.symm.toRingHom) ≫ Spec.map a₀ :=
    congrArg (fun g : Spec (.of L) ⟶ Spec (.of E) =>
      Spec.map (CommRingCat.ofHom σ.symm.toRingHom) ≫ g) hpre.symm
  exact h₁.trans ((Spec.map_comp a₀ (CommRingCat.ofHom σ.symm.toRingHom)).symm.trans
    (congrArg Spec.map hab))

/-- Every covering sieve of a finite Galois stage contains a canonical
transition to a larger finite Galois subfield of the fixed algebraic closure. -/
theorem exists_canonical_finiteGalois_mem_covering_sieve
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))
    (S : Sieve (finiteGaloisEtaleObject K E))
    (hS : S ∈ (Spec (.of K)).smallEtaleTopology _) :
    ∃ (L : FiniteGaloisIntermediateField K (AlgebraicClosure K))
      (h : E ⟶ L), S ((finiteGaloisEtaleDiagram K).map h.op) := by
  obtain ⟨L, f, hf⟩ := exists_finiteGalois_mem_covering_sieve_of_field_object
    K (finiteGaloisEtaleObject K E) (default : Spec (.of E)) S hS
  obtain ⟨h, t, ht⟩ := finiteGaloisEtaleHom_correct_to_canonical K E L f
  exact ⟨L, h, ht ▸ S.downward_closed hf t⟩

end EtaleCohomology

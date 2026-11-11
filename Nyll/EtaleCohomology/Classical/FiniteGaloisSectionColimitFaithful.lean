/- 
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FiniteGaloisSectionColimit

/-!
# Faithful finite-stage sections

Every canonical finite Galois transition is a surjective map of spectra.
Actual sheaf separatedness therefore makes every transition injective,
and each finite stage embeds in the actual section colimit.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry

namespace EtaleCohomology

/-- Restriction along a surjective map in the actual small etale site is injective. -/
theorem etaleSheaf_map_injective_of_surjective
    (X : Scheme.{u}) (F : Sheaf X.smallEtaleTopology (Type u))
    {V W : X.Etale} (f : V ⟶ W) (hf : Function.Surjective f.left) :
    Function.Injective (F.obj.map f.op) := by
  have hc : Sieve.ofArrows (fun _ : Unit => V) (fun _ => f) ∈
      X.smallEtaleTopology W := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff (fun _ : Unit => f)).mpr
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, hy⟩ := hf x
    exact Set.mem_iUnion.mpr ⟨(), y, hy⟩
  have hs : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology W := by
    apply X.smallEtaleTopology.superset_covering (R := _) ?_ hc
    intro Z g hg
    obtain ⟨a, k, rfl⟩ :=
      (Sieve.mem_ofArrows_iff (fun _ : Unit => V) (fun _ => f) g).mp hg
    exact (Sieve.generate (Presieve.singleton f)).downward_closed
      (Sieve.le_generate _ _ _ (Presieve.singleton_self _)) k
  have hF : Presieve.IsSheafFor F.obj (Presieve.singleton f) :=
    (Presieve.isSheafFor_iff_generate _).mpr
      ((isSheaf_iff_isSheaf_of_type _ _).mp F.property _ hs)
  exact Presieve.isSeparatedFor_singleton.mp hF.isSeparatedFor

variable (K : Type u) [Field K]
variable (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})

/-- Actual restrictions along canonical inclusions of finite Galois fields are injective. -/
theorem finiteGaloisSectionDiagram_map_injective
    {E L : FiniteGaloisIntermediateField K (AlgebraicClosure K)} (h : E ⟶ L) :
    Function.Injective ((finiteGaloisSectionDiagram K F).map h) := by
  let F₀ : Sheaf (Spec (.of K)).smallEtaleTopology (Type u) :=
    (sheafCompose (Spec (.of K)).smallEtaleTopology
      (forget AddCommGrpCat.{u})).obj F
  apply etaleSheaf_map_injective_of_surjective (Spec (.of K)) F₀
    ((finiteGaloisEtaleDiagram K).map h.op)
  change Function.Surjective
    (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h.le).toRingHom))
  intro x
  exact ⟨default, Subsingleton.elim _ _⟩

/-- Every finite-stage actual section embeds in the geometric section colimit. -/
theorem finiteGaloisSectionColimitι_injective
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    Function.Injective (finiteGaloisSectionColimitι K F E) := by
  intro s t hst
  obtain ⟨M, h, g, heq⟩ := (finiteGaloisSectionColimit_eq_iff K F s t).mp hst
  have hh : h = g := Subsingleton.elim _ _
  subst g
  exact finiteGaloisSectionDiagram_map_injective K F h heq

end EtaleCohomology

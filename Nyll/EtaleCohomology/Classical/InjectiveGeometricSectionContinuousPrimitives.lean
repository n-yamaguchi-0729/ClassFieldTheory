/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FiniteGaloisSectionTuples
public import Nyll.EtaleCohomology.Classical.FiniteGaloisSectionColimitTopology
public import Nyll.EtaleCohomology.Classical.InjectiveHomogeneousDeckPrimitives
public import Nyll.GaloisCohomology.Topology.ContinuousCochainTuples
public import Nyll.GaloisCohomology.Topology.ContinuousCohomologyRepresentatives
public import Nyll.GaloisCohomology.Topology.ContinuousTupleExactness

/-!
# Continuous primitives for actual injective geometric sections

Compactness realizes a continuous cocycle over one finite Galois field.
The proved actual geometric primitive there inflates to a continuous
primitive for the absolute Galois group.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry

namespace EtaleCohomology

variable (K : Type u) [Field K]
variable (I : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) [Injective I]

/-- Continuous homogeneous cocycles with actual injective geometric-section
coefficients have continuous equivariant primitives in every positive degree. -/
theorem exists_injective_geometricSection_continuous_primitive
    [TopologicalSpace (finiteGaloisSectionColimit K I)]
    [DiscreteTopology (finiteGaloisSectionColimit K I)]
    (n : ℕ)
    (z : C(Fin (n + 2) → Gal(AlgebraicClosure K/K), finiteGaloisSectionColimit K I))
    (heq : ∀ (σ : Gal(AlgebraicClosure K/K)) (a : Fin (n + 2) → Gal(AlgebraicClosure K/K)),
      z (fun i => σ * a i) = (finiteGaloisSectionColimitAction K I σ).asIso.hom (z a))
    (hc : ∀ a : Fin (n + 3) → Gal(AlgebraicClosure K/K),
      ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • z (fun j => a (i.succAbove j)) = 0) :
    ∃ g : C(Fin (n + 1) → Gal(AlgebraicClosure K/K), finiteGaloisSectionColimit K I),
      (∀ (σ : Gal(AlgebraicClosure K/K)) (a : Fin (n + 1) → Gal(AlgebraicClosure K/K)),
        g (fun i => σ * a i) = (finiteGaloisSectionColimitAction K I σ).asIso.hom (g a)) ∧
      ∀ a : Fin (n + 2) → Gal(AlgebraicClosure K/K),
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • g (fun j => a (i.succAbove j)) = z a := by
  classical
  obtain ⟨M, f, hf⟩ := exists_finiteGalois_section_tuple K I z z.continuous
  let r : Gal(AlgebraicClosure K/K) →* Gal(M/K) := AlgEquiv.restrictNormalHom M
  let j := finiteGaloisSectionColimitι K I M
  have heqM := finiteGalois_section_tuple_equivariant K I z M f hf heq
  have hcM (a : Fin (n + 3) → Gal(M/K)) :
      ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • f (fun k => a (i.succAbove k)) = 0 := by
    have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective _
    let b : Fin (n + 3) → Gal(AlgebraicClosure K/K) := fun i => (hr (a i)).choose
    have hb (i) : r (b i) = a i := (hr (a i)).choose_spec
    apply finiteGaloisSectionColimitι_injective K I M
    rw [map_sum, map_zero]
    have hsum : (∑ i : Fin (n + 3), j
        (((-1 : ℤ) ^ (i : ℕ)) • f (fun k => a (i.succAbove k)))) =
        ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • z (fun k => b (i.succAbove k)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_zsmul]
      apply congrArg (fun x => ((-1 : ℤ) ^ (i : ℕ)) • x)
      have ht : (fun k => r (b (i.succAbove k))) = (fun k => a (i.succAbove k)) :=
        funext (fun k => hb (i.succAbove k))
      exact (congrArg (fun c => j (f c)) ht).symm.trans
        (hf (fun k => b (i.succAbove k)))
    exact hsum.trans (hc b)
  obtain ⟨gM, hgM, hdM⟩ :=
    exists_injective_homogeneousFieldGalois_primitive K M I n f heqM hcM
  let g : C(Fin (n + 1) → Gal(AlgebraicClosure K/K), finiteGaloisSectionColimit K I) :=
    ⟨fun a => j (gM (fun i => r (a i))),
      (show Continuous (fun a : Fin (n + 1) → Gal(M/K) => j (gM a)) from
        continuous_of_discreteTopology).comp
        (continuous_pi fun i =>
          (InfiniteGalois.restrictNormalHom_continuous M.toIntermediateField).comp
            (continuous_apply i))⟩
  refine ⟨g, ?_, ?_⟩
  · intro σ a
    have ht : (fun i => r (σ * a i)) = (fun i => r σ * r (a i)) :=
      funext (fun i => map_mul r σ (a i))
    exact (congrArg (fun c => j (gM c)) ht).trans
      ((congrArg j (hgM (r σ) (fun i => r (a i)))).trans
        (ConcreteCategory.congr_hom (finiteGaloisSectionColimitAction_ι K I σ M)
          (gM (fun i => r (a i)))).symm)
  · intro a
    have h := congrArg j (hdM (fun i => r (a i)))
    have hm :
        j (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          gM (fun k => r (a (i.succAbove k)))) =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          j (gM (fun k => r (a (i.succAbove k)))) := by
      exact (map_sum j.hom _ Finset.univ).trans
        (Finset.sum_congr rfl (fun i _ =>
          map_zsmul j.hom ((-1 : ℤ) ^ (i : ℕ))
            (gM (fun k => r (a (i.succAbove k))))))
    exact hm.symm.trans (h.trans (hf a))

/-- Every positive-degree actual homogeneous continuous cocycle of injective
geometric sections is an actual homogeneous continuous coboundary. -/
theorem exists_injective_geometricSection_cochain_primitive
    (n : ℕ)
    (z : (TopRep.homogeneousCochains (finiteGaloisSectionColimitTopRep K I)).X (n + 1))
    (hz : (TopRep.homogeneousCochains (finiteGaloisSectionColimitTopRep K I)).d
      (n + 1) (n + 2) z = 0) :
    ∃ b : (TopRep.homogeneousCochains (finiteGaloisSectionColimitTopRep K I)).X n,
      (TopRep.homogeneousCochains (finiteGaloisSectionColimitTopRep K I)).d n (n + 1) b = z := by
  let A := finiteGaloisSectionColimitTopRep K I
  let : TopologicalSpace (finiteGaloisSectionColimit K I) := A.hV3
  have hD : DiscreteTopology (finiteGaloisSectionColimit K I) := ⟨rfl⟩
  exact TopRep.exists_homogeneousCochain_primitive_of_tuple_primitives
    Gal(AlgebraicClosure K/K) A n
    (fun f hf hc =>
      @exists_injective_geometricSection_continuous_primitive K _ I _
        A.hV3 hD n f hf hc)
    z hz

/-- Actual continuous Galois cohomology of the geometric sections of an injective
etale sheaf vanishes in every positive degree. -/
theorem continuousCohomology_injective_geometricSections_eq_zero
    (n : ℕ) (a : continuousCohomology (n + 1) (finiteGaloisSectionColimitTopRep K I)) :
    a = 0 :=
  TopRep.continuousCohomology_eq_zero_of_cochain_primitives
    Gal(AlgebraicClosure K/K) (finiteGaloisSectionColimitTopRep K I) n
    (exists_injective_geometricSection_cochain_primitive K I n) a

end EtaleCohomology

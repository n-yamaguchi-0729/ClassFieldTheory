/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.NormalizedGlobalFundamental
public import Nyll.GaloisCohomology.Topology.DiscreteOriginalH2Naturality

/-! # Changing the realization of the same finite top field -/

@[expose] public section

open CategoryTheory ClassFieldTheory.Brauer ContinuousCohomology NumberField
open scoped NumberField

noncomputable section
namespace GlobalClassFieldTheory.Cohomology

section IsomorphicInflation

variable (K : Type) [Field K] [NumberField K] {L E : Type}
  [Field L] [NumberField L] [Field E] [NumberField E] [Algebra K L] [Algebra K E]
  [Normal K L]

/-- Inflating through an isomorphism is precisely the standard field
transport on idèle classes. -/
theorem standardIdeleClassH2InflateOfEmbedding_eq_congrIso (e : L ≃ₐ[K] E) :
    standardIdeleClassH2InflateOfEmbedding e.toAlgHom = (standardIdeleClassH2CongrIso K e).hom := by
  let g := AlgEquiv.autCongr e
  have hg :
      (embeddedGaloisRestriction (B := K) e.toAlgHom).toMonoidHom = g.symm.toMonoidHom := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro a
    apply e.injective
    change e (embeddedGaloisRestriction (B := K) e.toAlgHom σ a) =
      e (e.symm (σ (e a)))
    rw [e.apply_symm_apply]
    exact embeddedGaloisRestriction_commutes (B := K) e.toAlgHom σ a
  rw [standardIdeleClassH2InflateOfEmbedding, standardIdeleClassH2CongrIso,
    groupCohomology.mapIso_hom]
  apply groupCohomology.map_congr hg
  apply LinearMap.ext
  intro a
  let a₀ : Additive (NumberField.IdeleClassGroup (𝓞 L) L) := a
  let c := Additive.toMul a₀
  apply Additive.toMul.injective
  let _ : Algebra L E := e.toRingHom.toAlgebra
  change NumberField.IdeleClassGroup.fieldInclusion L E c =
    NumberField.IdeleClassGroup.congr (e.restrictScalars ℚ) c
  have h := NumberField.IdeleClassGroup.congr_fieldInclusion
    (AlgEquiv.refl : L ≃ₐ[ℚ] L) (e.restrictScalars ℚ) (fun _ => rfl) c
  simpa only [NumberField.IdeleClassGroup.fieldInclusion_self, MonoidHom.id_apply,
    NumberField.IdeleClassGroup.congr_refl] using h.symm

end IsomorphicInflation

private theorem discreteGroupCohomologyInnerMap_eq_id
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G]
    (A : Rep ℤ G) (τ : G) (r : G →ₜ* G) (f : Rep.res r.toMonoidHom A ⟶ A)
    (hr : ∀ g, r g = τ⁻¹ * g * τ) (hf : ∀ x : A, f x = A.ρ τ x) :
    groupCohomology.map r.toMonoidHom f 2 = 𝟙 _ := by
  let X := TopRep.discreteCoefficientTopRep ℤ G A
  have hi := map_inner_eq_id_two X τ r (discreteTopRepMap r f) hr hf
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨y, rfl⟩ := (discreteTopRepH2Equiv A).surjective x
  change groupCohomology.map r.toMonoidHom f 2 (discreteTopRepH2Equiv A y) =
    discreteTopRepH2Equiv A y
  have hy : ContinuousCohomology.map r (discreteTopRepMap r f) 2 y = y :=
    (ConcreteCategory.congr_hom hi y).trans (ConcreteCategory.id_apply y)
  exact (discreteTopRepH2Equiv_map r f y).symm.trans
    (congrArg (discreteTopRepH2Equiv A) hy)

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

/-- Conjugating the original finite stage by a base-preserving field
automorphism acts trivially on the degree-two class cohomology. -/
theorem standardIdeleClassH2CongrIso_aut_hom_eq_id (τ : Gal(L/K)) :
    (standardIdeleClassH2CongrIso K τ).hom = 𝟙 _ := by
  let G := Gal(L/K)
  let A := standardIdeleClassRep K L
  let e := AlgEquiv.autCongr τ
  let r : G →ₜ* G :=
    { toMonoidHom := e.symm.toMonoidHom
      continuous_toFun := continuous_of_discreteTopology }
  let f : Rep.res r.toMonoidHom A ⟶ A :=
    Rep.ofHom ⟨A.ρ τ, fun a => by
      apply LinearMap.ext
      intro x
      change ((A.ρ τ * A.ρ (r a)) : A →ₗ[ℤ] A) x = (A.ρ a * A.ρ τ) x
      rw [← map_mul, ← map_mul]
      have h : τ * r a = a * τ := by
        change τ * (τ⁻¹ * a * τ) = a * τ
        group
      exact congrArg (fun g : G => A.ρ g x) h⟩
  have hf : (standardIdeleClassH2CongrIso K τ).hom = groupCohomology.map r.toMonoidHom f 2 := by
    rw [standardIdeleClassH2CongrIso, groupCohomology.mapIso_hom]
    apply groupCohomology.map_congr rfl
    apply LinearMap.ext
    intro a
    rfl
  exact hf.trans (discreteGroupCohomologyInnerMap_eq_id A τ r f (fun _ => rfl) (fun _ => rfl))

/-- Two embeddings of the same normal top field give the same inflation on
standard idèle-class cohomology. -/
theorem standardIdeleClassH2InflateOfEmbedding_eq_of_embeddings [Normal K L]
    {M : Type} [Field M] [NumberField M] [Algebra K M] (i j : L →ₐ[K] M) :
    standardIdeleClassH2InflateOfEmbedding i = standardIdeleClassH2InflateOfEmbedding j := by
  obtain ⟨τ, hτ⟩ := ClassFieldTheory.exists_embedding_comp_aut_eq_of_normal i j
  have hij : i = j.comp τ.toAlgHom := AlgHom.ext (fun a => (hτ a).symm)
  rw [hij, standardIdeleClassH2InflateOfEmbedding_comp,
    standardIdeleClassH2InflateOfEmbedding_eq_congrIso,
    standardIdeleClassH2CongrIso_aut_hom_eq_id, Category.id_comp]

end GlobalClassFieldTheory.Cohomology

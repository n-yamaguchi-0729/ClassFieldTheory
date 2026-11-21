/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteBaseChange
public import Nyll.ClassFieldTheory.Algebra.NormalEmbeddingRange
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.RestrictedAction
public import Nyll.GaloisCohomology.Topology.DiscreteCoefficientQuotient
public import Nyll.GaloisCohomology.Topology.DiscreteOriginalH2Naturality

/-! # Evaluating a finite tensor class in the separable closure of its base -/

@[expose] public section

open CategoryTheory ContinuousCohomology
open scoped ContRepresentation TensorProduct

noncomputable section
namespace ClassFieldTheory.Brauer

variable {K E F : Type} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [FiniteDimensional K E] [IsGalois K E]

local notation "G" => Gal(E/K)
local notation "T" => F ⊗[K] E
local notation "Ω" => SeparableClosure F

/-- The base algebra on the local separable closure induced by the completed field. -/
abbrev absoluteTensorClosureAlgebra (K F : Type) [Field K] [Field F] [Algebra K F] :
    Algebra K (SeparableClosure F) :=
  ((algebraMap F (SeparableClosure F)).comp (algebraMap K F)).toAlgebra

-- Keep the canonical F-algebra on the separable closure when the bases coincide.
attribute [local instance 50] absoluteTensorClosureAlgebra

theorem absoluteTensorClosureTower (K F : Type) [Field K] [Field F] [Algebra K F] :
    IsScalarTower K F (SeparableClosure F) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

attribute [local instance 50] absoluteTensorClosureTower
attribute [local instance] scalarTensorUnitsAction

local notation "A" => Rep.ofMulDistribMulAction G Tˣ

/-- The finite tensor coefficient representation with its discrete topology. -/
abbrev tensorUnitsTopRep : TopRep.{0} ℤ G := TopRep.discreteCoefficientTopRep ℤ G A

local notation "Xₜ" => tensorUnitsTopRep (K := K) (E := E) (F := F)

/-- Evaluate a local tensor through a specified embedding of the top field
and the canonical inclusion of the completed base. -/
def absoluteTensorEvaluation (j : E →ₐ[K] Ω) : T →ₐ[F] Ω :=
  Algebra.TensorProduct.lift (Algebra.ofId F Ω) j (fun _ _ => Commute.all _ _)

omit [FiniteDimensional K E] [IsGalois K E] in
theorem absoluteTensorEvaluation_tmul (j : E →ₐ[K] Ω) (a : F) (x : E) :
    absoluteTensorEvaluation j (a ⊗ₜ[K] x) = algebraMap F Ω a * j x :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

omit [FiniteDimensional K E] in
theorem absoluteTensorEvaluation_conjugation (j : E →ₐ[K] Ω) (σ : Gal(Ω/F)) (a : T) :
    absoluteTensorEvaluation j (scalarTensorConjugation (embeddedGaloisRestriction j σ) a) =
      σ (absoluteTensorEvaluation j a) := by
  induction a using TensorProduct.inductionOn with
  | add b c hb hc => simp only [map_add, hb, hc]
  | tmul b x =>
    rw [scalarTensorConjugation_tmul, absoluteTensorEvaluation_tmul,
      absoluteTensorEvaluation_tmul, map_mul, embeddedGaloisRestriction_commutes, σ.commutes]

/-- Restriction of the Galois action followed by the actual tensor evaluation. -/
def absoluteTensorUnitsMap (j : E →ₐ[K] Ω) :
    let r : Gal(Ω/F) →ₜ* G := embeddedGaloisRestriction (B := F) j
    TopRep.res r.toMonoidHom Xₜ ⟶ unitsRep F := by
  intro r
  let D := TopRep.res r.toMonoidHom Xₜ
  let Y := unitsRep F
  let : DiscreteTopology D := TopRep.discreteCoefficientTopRep_discrete ℤ G A
  let : Module ℤ D := D.hV2
  let : Module ℤ Y := Y.hV2
  let f : D →ₗ[ℤ] Y :=
    (Units.map (absoluteTensorEvaluation j).toMonoidHom).toAdditive.toIntLinearMap
  let φ : D.ρ →ⁱL Y.ρ :=
    { toLinearMap := f
      cont := continuous_of_discreteTopology
      isIntertwining' := fun σ => by
        apply ContinuousLinearMap.ext
        intro a
        apply Additive.toMul.injective
        apply Units.ext
        let a' : Additive Tˣ := a
        exact absoluteTensorEvaluation_conjugation j σ (a'.toMul : T) }
  exact ConcreteCategory.ofHom φ

omit [FiniteDimensional K E] in
theorem absoluteTensorUnitsMap_apply (j : E →ₐ[K] Ω) (a : Additive Tˣ) :
    absoluteTensorUnitsMap j a =
      Additive.ofMul (Units.map (absoluteTensorEvaluation j).toMonoidHom a.toMul) :=
  rfl

/-- A tensor cohomology class evaluated directly in the absolute Brauer group. -/
def absoluteTensorH2Map (j : E →ₐ[K] Ω) : groupCohomology A 2 →+ Br F := by
  let r : Gal(Ω/F) →ₜ* G := embeddedGaloisRestriction (B := F) j
  let m : continuousCohomology 2 Xₜ ⟶ continuousCohomology 2 (unitsRep F) :=
    ContinuousCohomology.map r (absoluteTensorUnitsMap j) 2
  exact m.hom.toLinearMap.toAddMonoidHom.comp (discreteTopRepH2Equiv A).symm.toAddMonoidHom

omit [IsGalois K E] in
/-- The discrete comparison on field units is the original one on cocycles. -/
theorem galoisUnitsDiscreteH2_eq_original (x : continuousCohomology 2 (galoisUnitsRep K E)) :
    discreteTopRepH2Equiv (Rep.ofAlgebraAutOnUnits K E) x =
      discreteOriginalH2Equiv (galoisUnitsRep K E) x := by
  let U := Rep.ofAlgebraAutOnUnits K E
  let Q := TopRep.discreteCoefficientTopRep ℤ G U
  obtain ⟨c, rfl⟩ := π_surjective Q 2 x
  change discreteTopRepH2Equiv U (π Q 2 c) = discreteOriginalH2Equiv Q (π Q 2 c)
  rw [discreteTopRepH2Equiv_π U, discreteOriginalH2Equiv_π Q]
  apply congrArg (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K E))
  apply groupCohomology.cocycles₂_ext
  intro g h
  rfl

omit [FiniteDimensional K E] [IsGalois K E] in
/-- Composing a chosen embedding with a global automorphism acts by that
automorphism on the right tensor factor. -/
theorem absoluteTensorEvaluation_comp_aut (j : E →ₐ[K] Ω) (τ : G) (a : T) :
    absoluteTensorEvaluation (j.comp τ.toAlgHom) a =
      absoluteTensorEvaluation j (scalarTensorConjugation τ a) := by
  induction a using TensorProduct.inductionOn with
  | add b c hb hc => simp only [map_add, hb, hc]
  | tmul b x =>
    rw [absoluteTensorEvaluation_tmul, scalarTensorConjugation_tmul,
      absoluteTensorEvaluation_tmul, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply]

/-- The absolute class of a tensor cocycle is independent of its chosen top-field embedding. -/
theorem absoluteTensorH2Map_eq_of_embeddings (i j : E →ₐ[K] Ω) :
    absoluteTensorH2Map i = absoluteTensorH2Map j := by
  obtain ⟨τ, hτ⟩ := ClassFieldTheory.exists_embedding_comp_aut_eq_of_normal i j
  have hie : i = j.comp τ.toAlgHom := AlgHom.ext (fun a => (hτ a).symm)
  subst i
  let c : G →ₜ* G :=
    { toFun := fun g => τ⁻¹ * g * τ
      map_one' := by group
      map_mul' := fun g h => by group
      continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const }
  have hc (g : G) : τ * c g = g * τ := by
    change τ * (τ⁻¹ * g * τ) = g * τ
    group
  let a : TopRep.res c.toMonoidHom Xₜ ⟶ Xₜ :=
    ConcreteCategory.ofHom
      { toContinuousLinearMap := (Xₜ).ρ τ
        isIntertwining' := fun g => by
          apply ContinuousLinearMap.ext
          intro x
          change (((Xₜ).ρ τ * (Xₜ).ρ (c g)) : Xₜ →L[ℤ] Xₜ) x =
            ((Xₜ).ρ g * (Xₜ).ρ τ) x
          rw [← map_mul, ← map_mul, hc] }
  let r := embeddedGaloisRestriction (B := F) j
  let p := absoluteTensorUnitsMap j
  let s := embeddedGaloisRestriction (B := F) (j.comp τ.toAlgHom)
  let q := absoluteTensorUnitsMap (j.comp τ.toAlgHom)
  have hg (g : Gal(Ω/F)) : s g = c (r g) := by
    apply AlgEquiv.ext
    intro x
    apply τ.injective
    apply j.injective
    have h := congrArg (fun σ : G => σ x) (hc (r g))
    change τ (c (r g) x) = r g (τ x) at h
    calc
      (j.comp τ.toAlgHom) (s g x) = g ((j.comp τ.toAlgHom) x) :=
        embeddedGaloisRestriction_commutes (j.comp τ.toAlgHom) g x
      _ = j (r g (τ x)) := (embeddedGaloisRestriction_commutes j g (τ x)).symm
      _ = j (τ (c (r g) x)) := congrArg j h.symm
  have hm := map_eq_of_values 2 (r := s) (s := c.comp r) q
    ((TopRep.resFunctor r.toMonoidHom).map
      (X := TopRep.res c.toMonoidHom Xₜ) (Y := Xₜ) a ≫ p)
    hg (fun x => by
      apply Additive.toMul.injective
      apply Units.ext
      let x' : Additive Tˣ := x
      exact absoluteTensorEvaluation_comp_aut j τ (x'.toMul : T))
  rw [ContinuousCohomology.map_comp,
    map_inner_eq_id_two Xₜ τ c a (fun _ => rfl) (fun _ => rfl), Category.id_comp] at hm
  apply AddMonoidHom.ext
  intro x
  exact ConcreteCategory.congr_hom hm _

end ClassFieldTheory.Brauer

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.AbsoluteTensorEvaluation

/-! # Absolute localization is unchanged under inflation of the top field -/

@[expose] public section

open CategoryTheory ContinuousCohomology
open scoped TensorProduct

noncomputable section
namespace ClassFieldTheory.Brauer

variable {K M E F : Type} [Field K] [Field M] [Field E] [Field F]
  [Algebra K M] [Algebra K E] [Algebra K F] [FiniteDimensional K M] [FiniteDimensional K E]
  [IsGalois K M] [IsGalois K E]

local notation "Ω" => SeparableClosure F
attribute [local instance 50] absoluteTensorClosureAlgebra absoluteTensorClosureTower
attribute [local instance] scalarTensorUnitsAction
local notation "A" L => Rep.ofMulDistribMulAction Gal(L/K) (F ⊗[K] L)ˣ

/-- Scalar inclusion of the upper tensor factor, as a map of coefficients for inflation. -/
def tensorTopFieldInflationRepHom (j : M →ₐ[K] E) :
    Rep.res (embeddedGaloisRestriction (B := K) j).toMonoidHom (A M) ⟶ A E := by
  let i := Algebra.TensorProduct.map (AlgHom.id K F) j
  refine Rep.ofHom ⟨(Units.map i.toMonoidHom).toAdditive.toIntLinearMap, fun σ => ?_⟩
  apply LinearMap.ext
  intro u
  apply Additive.toMul.injective
  apply Units.ext
  let a : Additive (F ⊗[K] M)ˣ := u
  change i (scalarTensorConjugation (embeddedGaloisRestriction (B := K) j σ)
      (a.toMul : F ⊗[K] M)) = scalarTensorConjugation σ (i (a.toMul : F ⊗[K] M))
  generalize (a.toMul : F ⊗[K] M) = z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    simp only [i, scalarTensorConjugation_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      embeddedGaloisRestriction_commutes]

omit [FiniteDimensional K M] [FiniteDimensional K E] [IsGalois K M] [IsGalois K E] in
private theorem absoluteTensorEvaluation_topFieldMap (j : M →ₐ[K] E) (i : E →ₐ[K] Ω)
    (z : F ⊗[K] M) :
    absoluteTensorEvaluation (i.comp j) z =
      absoluteTensorEvaluation i (Algebra.TensorProduct.map (AlgHom.id K F) j z) := by
  induction z using TensorProduct.inductionOn with
  | add b c hb hc => simp only [map_add, hb, hc]
  | tmul b c =>
    simp only [absoluteTensorEvaluation_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      AlgHom.comp_apply]

/-- Actual inflation of the finite top field preserves the local absolute class. -/
theorem absoluteTensorH2Map_topFieldInflation (j : M →ₐ[K] E) (i : E →ₐ[K] Ω)
    (x : groupCohomology (A M) 2) :
    absoluteTensorH2Map i (groupCohomology.map (embeddedGaloisRestriction (B := K) j).toMonoidHom
        (tensorTopFieldInflationRepHom (F := F) j) 2 x) =
      absoluteTensorH2Map (i.comp j) x := by
  let r := embeddedGaloisRestriction (B := K) j
  let s := embeddedGaloisRestriction (B := F) i
  let t := embeddedGaloisRestriction (B := F) (i.comp j)
  let p := tensorTopFieldInflationRepHom (F := F) j
  let α := discreteTopRepMap r p
  let β := absoluteTensorUnitsMap i
  let q := absoluteTensorUnitsMap (i.comp j)
  have hg (σ : Gal(Ω/F)) : t σ = r (s σ) := by
    apply AlgEquiv.ext
    intro a
    apply (i.comp j).injective
    change (i.comp j) (t σ a) = i (j (r (s σ) a))
    calc
      _ = σ ((i.comp j) a) :=
        embeddedGaloisRestriction_commutes (B := F) (i.comp j) σ a
      _ = i (s σ (j a)) :=
        (embeddedGaloisRestriction_commutes (B := F) i σ (j a)).symm
      _ = _ :=
        congrArg i (embeddedGaloisRestriction_commutes (B := K) j (s σ) a).symm
  have hcoeff (a : Additive (F ⊗[K] M)ˣ) : q a = β (α a) := by
    let b : Additive (F ⊗[K] E)ˣ := α a
    refine (absoluteTensorUnitsMap_apply (i.comp j) a).trans
      (Eq.trans ?_ (absoluteTensorUnitsMap_apply i b).symm)
    apply congrArg (Additive.ofMul : Ωˣ → Additive Ωˣ)
    apply Units.ext
    change absoluteTensorEvaluation (i.comp j) (a.toMul : F ⊗[K] M) =
      absoluteTensorEvaluation i (Algebra.TensorProduct.map (AlgHom.id K F) j a.toMul)
    exact absoluteTensorEvaluation_topFieldMap j i a.toMul
  let X := tensorUnitsTopRep (K := K) (E := M) (F := F)
  let Y := tensorUnitsTopRep (K := K) (E := E) (F := F)
  let αs : TopRep.res (r.comp s).toMonoidHom X ⟶ TopRep.res s.toMonoidHom Y :=
    (TopRep.resFunctor s.toMonoidHom).map (X := TopRep.res r.toMonoidHom X) (Y := Y) α
  have hm : ContinuousCohomology.map t q 2 =
      ContinuousCohomology.map r α 2 ≫ ContinuousCohomology.map s β 2 := by
    rw [← ContinuousCohomology.map_comp]
    exact map_eq_of_values 2 (r := t) (s := r.comp s) q (αs ≫ β) hg hcoeff
  let z := (discreteTopRepH2Equiv (A M)).symm x
  have hz := discreteTopRepH2Equiv_map r p z
  rw [show discreteTopRepH2Equiv (A M) z = x from
    (discreteTopRepH2Equiv (A M)).apply_symm_apply x] at hz
  have he : (discreteTopRepH2Equiv (A E)).symm (groupCohomology.map r.toMonoidHom p 2 x) =
      ContinuousCohomology.map r α 2 z :=
    ((discreteTopRepH2Equiv (A E)).symm_apply_eq).mpr hz.symm
  change ContinuousCohomology.map s β 2
      ((discreteTopRepH2Equiv (A E)).symm (groupCohomology.map r.toMonoidHom p 2 x)) = _
  rw [he]
  exact (ConcreteCategory.congr_hom hm z).symm

end ClassFieldTheory.Brauer

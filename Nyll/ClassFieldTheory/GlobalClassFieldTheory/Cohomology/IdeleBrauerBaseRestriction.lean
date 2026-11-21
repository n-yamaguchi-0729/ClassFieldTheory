/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.RestrictionNaturality
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.AbsoluteTensorShapiro
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.IdeleTensorBaseRestriction

/-! # Restriction of actual idèle cocycles on local Brauer coordinates -/

@[expose] public section

open CategoryTheory ClassFieldTheory.Brauer ContinuousCohomology
open Field.absoluteGaloisGroup
open scoped TensorProduct

noncomputable section
namespace GlobalClassFieldTheory.Cohomology

variable {K M E F H : Type} [Field K] [Field M] [Field E] [Field F] [Field H]
  [Algebra K M] [Algebra M E] [Algebra K E] [IsScalarTower K M E]
  [Algebra K F] [Algebra K H] [Algebra M H] [IsScalarTower K M H]
  [FiniteDimensional K E] [FiniteDimensional M E] [IsGalois K E] [IsGalois M E]

local notation "ΩF" => SeparableClosure F
local notation "ΩH" => SeparableClosure H
attribute [local instance 50] absoluteTensorClosureAlgebra absoluteTensorClosureTower

local instance (priority := 50) : IsScalarTower K M ΩH := by
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  change algebraMap H ΩH (algebraMap K H x) = algebraMap H ΩH (algebraMap M H (algebraMap K M x))
  rw [IsScalarTower.algebraMap_apply K M H]

local instance : MulDistribMulAction Gal(E/K) (F ⊗[K] E)ˣ := scalarTensorUnitsAction
local instance : MulDistribMulAction Gal(E/M) (H ⊗[M] E)ˣ := scalarTensorUnitsAction
local notation "A" => Rep.ofMulDistribMulAction Gal(E/K) (F ⊗[K] E)ˣ
local notation "Bₜ" => Rep.ofMulDistribMulAction Gal(E/M) (H ⊗[M] E)ˣ

/-- Actual base change of the tensor coefficients gives absolute restriction
of the local Brauer class. The top field and its automorphisms are unchanged. -/
theorem absoluteTensorH2Map_baseRestriction (f : F →ₐ[K] H)
    (i : E →ₐ[K] ΩF) (j : E →ₐ[M] ΩH) (x : groupCohomology A 2) :
    absoluteTensorH2Map j
        (groupCohomology.map (AlgEquiv.restrictScalarsHom K)
          (localTensorBaseRestrictionRepHom (L₀ := E) f) 2 x) =
      restrict f.toRingHom (absoluteTensorH2Map i x) := by
  let u := separableClosureLift f.toRingHom
  let s := separableMap f.toRingHom
  have hJ (a : K) : u (algebraMap K ΩF a) = algebraMap K ΩH a := by
    change u (algebraMap F ΩF (algebraMap K F a)) =
      algebraMap H ΩH (algebraMap K H a)
    exact (separableClosureLift_algebraMap f.toRingHom (algebraMap K F a)).trans
      (congrArg (algebraMap H ΩH) (f.commutes a))
  let J : ΩF →ₐ[K] ΩH := ⟨u, hJ⟩
  let i' := J.comp i
  let j' := j.restrictScalars K
  let r : Gal(E/M) →ₜ* Gal(E/K) :=
    { toMonoidHom := AlgEquiv.restrictScalarsHom K
      continuous_toFun := InfiniteGalois.restrictScalarsHom_continuous K M E }
  let r₀ : Gal(E/K) →ₜ* Gal(E/K) := ContinuousMonoidHom.id _
  let P := Rep.ofMulDistribMulAction Gal(E/K) (H ⊗[K] E)ˣ
  let p₀ : Rep.res r₀.toMonoidHom A ⟶ P :=
    localTensorBaseRestrictionRepHom (M₀ := K) (L₀ := E) f
  let p₁ : Rep.res r.toMonoidHom P ⟶ Bₜ :=
    localTensorBaseRestrictionRepHom (M₀ := M) (L₀ := E) (AlgHom.id K H)
  let p : Rep.res r.toMonoidHom A ⟶ Bₜ :=
    localTensorBaseRestrictionRepHom (M₀ := M) (L₀ := E) f
  let xH := groupCohomology.map r₀.toMonoidHom p₀ 2 x
  have hTensor (a : F ⊗[K] E) :
      localTensorBaseRestriction K M E (AlgHom.id K H)
          (localTensorBaseRestriction K K E f a) =
        localTensorBaseRestriction K M E f a := by
    induction a using TensorProduct.inductionOn with
    | add b c hb hc => simp only [map_add, hb, hc]
    | tmul b c =>
      rw [localTensorBaseRestriction_tmul, localTensorBaseRestriction_tmul,
        localTensorBaseRestriction_tmul]
      rfl
  have hMaps : groupCohomology.map r₀.toMonoidHom p₀ 2 ≫
      groupCohomology.map r.toMonoidHom p₁ 2 = groupCohomology.map r.toMonoidHom p 2 := by
    refine (groupCohomology.map_comp r₀.toMonoidHom r.toMonoidHom p₀ p₁ 2).symm.trans ?_
    apply groupCohomology.map_congr
    · exact MonoidHom.id_comp _
    · apply LinearMap.ext
      intro a
      apply Additive.toMul.injective
      apply Units.ext
      let a₀ : Additive (F ⊗[K] E)ˣ := a
      exact hTensor a₀.toMul.val
  let α₀ := discreteTopRepMap r₀ p₀
  let α₁ := discreteTopRepMap r p₁
  let β := absoluteTensorUnitsMap (F := H) j
  let β' := absoluteTensorUnitsMap (F := H) j'
  let γ := absoluteTensorUnitsMap (F := F) i
  let γ' := absoluteTensorUnitsMap (F := H) i'
  let δ := galoisUnitsMap s u (separableMap_commutes f.toRingHom)
  let rj := embeddedGaloisRestriction (B := H) j
  let ri := embeddedGaloisRestriction (B := F) i
  let rj' := embeddedGaloisRestriction (B := H) j'
  let ri' := embeddedGaloisRestriction (B := H) i'
  have hg₁ (σ : Gal(ΩH/H)) : rj' σ = r (rj σ) := by
    apply AlgEquiv.ext
    intro a
    apply j'.injective
    change j' (rj' σ a) = j (rj σ a)
    exact (embeddedGaloisRestriction_commutes j' σ a).trans
      (embeddedGaloisRestriction_commutes j σ a).symm
  have hg₂ (σ : Gal(ΩH/H)) : r₀ (ri' σ) = ri (s σ) := by
    apply AlgEquiv.ext
    intro a
    apply i'.injective
    change i' (ri' σ a) = u (i (ri (s σ) a))
    exact (embeddedGaloisRestriction_commutes i' σ a).trans
      ((congrArg u (embeddedGaloisRestriction_commutes i (s σ) a)).trans
        (separableMap_commutes f.toRingHom σ (i a))).symm
  have hEval₁ (a : H ⊗[K] E) :
      absoluteTensorEvaluation (F := H) j' a =
        absoluteTensorEvaluation (F := H) j
          (localTensorBaseRestriction K M E (AlgHom.id K H) a) := by
    induction a using TensorProduct.inductionOn with
    | add b c hb hc => simp only [map_add, hb, hc]
    | tmul b c =>
      rw [absoluteTensorEvaluation_tmul, localTensorBaseRestriction_tmul,
        absoluteTensorEvaluation_tmul]
      rfl
  have hEval₂ (a : F ⊗[K] E) :
      absoluteTensorEvaluation (F := H) i' (localTensorBaseRestriction K K E f a) =
        u (absoluteTensorEvaluation (F := F) i a) := by
    induction a using TensorProduct.inductionOn with
    | add b c hb hc => simp only [map_add, hb, hc]
    | tmul b c =>
      rw [localTensorBaseRestriction_tmul, absoluteTensorEvaluation_tmul,
        absoluteTensorEvaluation_tmul, map_mul, separableClosureLift_algebraMap]
      rfl
  have h₁ := map_eq_of_values 2 (r := rj') (s := r.comp rj)
    β' ((TopRep.resFunctor rj.toMonoidHom).map α₁ ≫ β) hg₁ (fun a => by
      apply Additive.toMul.injective
      apply Units.ext
      let a₀ : Additive (H ⊗[K] E)ˣ := a
      exact hEval₁ a₀.toMul.val)
  have h₂ := map_eq_of_values 2 (r := r₀.comp ri') (s := ri.comp s)
    ((TopRep.resFunctor ri'.toMonoidHom).map α₀ ≫ γ')
    ((TopRep.resFunctor s.toMonoidHom).map γ ≫ δ) hg₂ (fun a => by
      apply Additive.toMul.injective
      apply Units.ext
      let a₀ : Additive (F ⊗[K] E)ˣ := a
      exact hEval₂ a₀.toMul.val)
  have ht₁ := h₁.trans (ContinuousCohomology.map_comp r rj α₁ β 2)
  have ht₂ := (ContinuousCohomology.map_comp r₀ ri' α₀ γ' 2).symm.trans
    (h₂.trans (ContinuousCohomology.map_comp ri s γ δ 2))
  let z := (discreteTopRepH2Equiv A).symm x
  let zH := (discreteTopRepH2Equiv P).symm xH
  have hZ : ContinuousCohomology.map r₀ α₀ 2 z = zH := by
    apply (discreteTopRepH2Equiv P).injective
    exact (discreteTopRepH2Equiv_map r₀ p₀ z).trans
      ((congrArg (groupCohomology.map r₀.toMonoidHom p₀ 2)
        ((discreteTopRepH2Equiv A).apply_symm_apply x)).trans
          ((discreteTopRepH2Equiv P).apply_symm_apply xH).symm)
  let y := groupCohomology.map r.toMonoidHom p 2 x
  have hMap := ConcreteCategory.congr_hom hMaps x
  have hY : ContinuousCohomology.map r α₁ 2 zH = (discreteTopRepH2Equiv Bₜ).symm y := by
    apply (discreteTopRepH2Equiv Bₜ).injective
    exact (discreteTopRepH2Equiv_map r p₁ zH).trans
      ((congrArg (groupCohomology.map r.toMonoidHom p₁ 2)
        ((discreteTopRepH2Equiv P).apply_symm_apply xH)).trans
          (hMap.trans ((discreteTopRepH2Equiv Bₜ).apply_symm_apply y).symm))
  have hLeft : absoluteTensorH2Map j' xH = absoluteTensorH2Map j y := by
    exact (ConcreteCategory.congr_hom ht₁ zH).trans
      (congrArg (ContinuousCohomology.map rj β 2) hY)
  have hRight : absoluteTensorH2Map i' xH = restrict f.toRingHom (absoluteTensorH2Map i x) :=
    (congrArg (ContinuousCohomology.map ri' γ' 2) hZ.symm).trans
      (ConcreteCategory.congr_hom ht₂ z)
  have hCompare := DFunLike.congr_fun (absoluteTensorH2Map_eq_of_embeddings j' i') xH
  exact hLeft.symm.trans (hCompare.trans hRight)

end GlobalClassFieldTheory.Cohomology

namespace GlobalClassFieldTheory.Cohomology

variable {K E F H : Type} [Field K] [Field E] [Field F] [Field H]
  [Algebra K E] [Algebra K F] [Algebra K H] [Algebra E H] [IsScalarTower K E H]
  [FiniteDimensional K E] [IsGalois K E]

attribute [local instance 50] absoluteTensorClosureAlgebra absoluteTensorClosureTower

local instance : MulDistribMulAction Gal(E/K) (F ⊗[K] E)ˣ := scalarTensorUnitsAction

/-- Restricting a tensor class to an actual completed field containing the
top field kills the class. -/
theorem restrict_absoluteTensorH2Map_eq_zero_of_embedding (f : F →ₐ[K] H)
    (i : E →ₐ[K] SeparableClosure F)
    (x : groupCohomology (Rep.ofMulDistribMulAction Gal(E/K) (F ⊗[K] E)ˣ) 2) :
    restrict f.toRingHom (absoluteTensorH2Map i x) = 0 := by
  let j := Algebra.ofId E (SeparableClosure H)
  have hr : (AlgEquiv.restrictScalarsHom K : Gal(E/E) →* Gal(E/K)) = 1 := by
    apply MonoidHom.ext
    intro σ
    exact (congrArg (AlgEquiv.restrictScalarsHom K) (Subsingleton.elim σ 1)).trans (map_one _)
  let p := localTensorBaseRestrictionRepHom (M₀ := E) (L₀ := E) f
  let r := (AlgEquiv.restrictScalarsHom K : Gal(E/E) →* Gal(E/K))
  have h₀ := groupCohomology.map_eq_zero (f := r) (φ := p) 2 hr
  have hx : groupCohomology.map r p 2 x = 0 :=
    ConcreteCategory.congr_hom h₀ x
  have h := absoluteTensorH2Map_baseRestriction (M := E) f i j x
  exact h.symm.trans ((congrArg (absoluteTensorH2Map j) hx).trans (map_zero _))

end GlobalClassFieldTheory.Cohomology

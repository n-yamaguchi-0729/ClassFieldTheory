/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionLinearDisjoint
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FullConstants
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree
import Nyll.GaloisCohomology.Topology.GaloisRestrictionScalars

/-!
# The actual constant-field degree on an absolute Galois group

Restriction to the separable closure of the constants is continuous. Its image
is closed by compactness. If the original field has no extra separable constants,
the fixed field of that image is the constant base, so Galois correspondence
proves surjectivity. Arithmetic Frobenius coordinates then give the degree map.
-/

noncomputable section

namespace FunctionField

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra k Ω] [Algebra K Ω] [IsScalarTower k K Ω]
    [IsSepClosed Ω]

/-- Restriction of actual automorphisms to the constants in the separable closure. -/
def absoluteConstantRestriction :
    (Ω ≃ₐ[K] Ω) →ₜ* (separableClosure k Ω ≃ₐ[k] separableClosure k Ω) where
  toMonoidHom := (AlgEquiv.restrictNormalHom (separableClosure k Ω)).comp
    (AlgEquiv.restrictScalarsHom k)
  continuous_toFun :=
    (InfiniteGalois.restrictNormalHom_continuous (separableClosure k Ω)).comp
      (InfiniteGalois.restrictScalarsHom_continuous k K Ω)

variable [IsGalois K Ω]

omit [Finite k] in
/-- Full separable constants make the actual restriction map onto. -/
theorem absoluteConstantRestriction_surjective
    (hsc : ∀ y : K, IsSeparable k y → y ∈ (algebraMap k K).range) :
    Function.Surjective (absoluteConstantRestriction k K Ω) := by
  let C := separableClosure k Ω
  let r := absoluteConstantRestriction k K Ω
  let H : ClosedSubgroup (C ≃ₐ[k] C) :=
    ⟨r.toMonoidHom.range, r.continuous_toFun.isClosedMap.isClosed_range⟩
  have hfix : IntermediateField.fixedField H.toSubgroup = ⊥ := by
    apply bot_unique
    intro c hc
    have hfixed : ∀ σ : Ω ≃ₐ[K] Ω, σ (c : Ω) = (c : Ω) := by
      intro σ
      rw [IntermediateField.mem_fixedField_iff] at hc
      have h := hc (r σ) ⟨σ, rfl⟩
      have hr := AlgEquiv.restrictNormal_commutes (σ.restrictScalars k) C c
      exact hr.symm.trans (congrArg Subtype.val h)
    obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (K := Ω)
      (c : Ω)).mpr hfixed
    have hyC : algebraMap K Ω y ∈ separableClosure k Ω := hy.symm ▸ c.property
    have hysep : IsSeparable k y := mem_separableClosure_iff.mp
      ((map_mem_separableClosure_iff (IsScalarTower.toAlgHom k K Ω)).mp hyC)
    obtain ⟨a, ha⟩ := hsc y hysep
    apply IntermediateField.mem_bot.mpr
    refine ⟨a, Subtype.ext ?_⟩
    change algebraMap k Ω a = (c : Ω)
    rw [IsScalarTower.algebraMap_apply k K Ω, ha, hy]
  have htop : H.toSubgroup = ⊤ := by
    rw [← InfiniteGalois.fixingSubgroup_fixedField H, hfix,
      IntermediateField.fixingSubgroup_bot]
  exact MonoidHom.range_eq_top.mp htop

/-- The arithmetic degree of an automorphism, measured on the actual constant closure. -/
def absoluteConstantDegree : (Ω ≃ₐ[K] Ω) →ₜ* ClassFormation.ZHatMul := by
  let : Fintype k := Fintype.ofFinite k
  have : IsSepClosed (separableClosure k Ω) := IsSepClosure.sep_closed k
  have : PerfectField (separableClosure k Ω) := Algebra.IsAlgebraic.perfectField k
  exact (LocalClassFieldTheory.residueAbsoluteDegreeIn k (separableClosure k Ω)).comp
    (absoluteConstantRestriction k K Ω)

/-- With full separable constants, every profinite degree occurs. -/
theorem absoluteConstantDegree_surjective
    (hsc : ∀ y : K, IsSeparable k y → y ∈ (algebraMap k K).range) :
    Function.Surjective (absoluteConstantDegree k K Ω) := by
  let : Fintype k := Fintype.ofFinite k
  have : IsSepClosed (separableClosure k Ω) := IsSepClosure.sep_closed k
  have : PerfectField (separableClosure k Ω) := Algebra.IsAlgebraic.perfectField k
  exact (LocalClassFieldTheory.residueAbsoluteFrobeniusEquivIn k
    (separableClosure k Ω)).symm.surjective.comp
      (absoluteConstantRestriction_surjective k K Ω hsc)

omit [IsGalois K Ω] in
/-- Degree zero means that every actual algebraic constant is fixed. -/
theorem absoluteConstantDegree_eq_one_iff (σ : Ω ≃ₐ[K] Ω) :
    absoluteConstantDegree k K Ω σ = 1 ↔
      ∀ c : separableClosure k Ω, σ (c : Ω) = (c : Ω) := by
  let : Fintype k := Fintype.ofFinite k
  have : IsSepClosed (separableClosure k Ω) := IsSepClosure.sep_closed k
  have : PerfectField (separableClosure k Ω) := Algebra.IsAlgebraic.perfectField k
  change (LocalClassFieldTheory.residueAbsoluteFrobeniusEquivIn k
    (separableClosure k Ω)).symm.toMulEquiv (absoluteConstantRestriction k K Ω σ) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff]
  constructor
  · intro h c
    have hr := AlgEquiv.restrictNormal_commutes (σ.restrictScalars k)
      (separableClosure k Ω) c
    have hc := congrArg (fun τ : separableClosure k Ω ≃ₐ[k] separableClosure k Ω =>
      (τ c : Ω)) h
    exact hr.symm.trans hc
  · intro h
    apply AlgEquiv.ext
    intro c
    apply Subtype.ext
    exact (AlgEquiv.restrictNormal_commutes (σ.restrictScalars k)
      (separableClosure k Ω) c).trans (h c)

omit [IsGalois K Ω] in
/-- The kernel fixes precisely the actual compositum with all algebraic constants. -/
theorem absoluteConstantDegree_ker :
    (absoluteConstantDegree k K Ω).toMonoidHom.ker =
      (IntermediateField.adjoin K (separableClosure k Ω : Set Ω)).fixingSubgroup := by
  ext σ
  change absoluteConstantDegree k K Ω σ = 1 ↔ _
  rw [absoluteConstantDegree_eq_one_iff,
    IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h
    let F := IntermediateField.adjoin K (separableClosure k Ω : Set Ω)
    have heq : σ.toAlgHom.comp F.val = F.val := by
      apply IntermediateField.adjoin_algHom_ext K
      intro c hc
      exact h ⟨c, hc⟩
    intro x hx
    exact DFunLike.congr_fun heq ⟨x, hx⟩
  · intro h c
    exact h (c : Ω) (IntermediateField.subset_adjoin K _ c.property)

end FunctionField

namespace FunctionField

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω] [IsGalois K Ω]

/-- The concrete degree datum on the actual function-field absolute Galois group.
The original finite base is replaced by its proved full constant field. -/
def fullConstantDegreeData : ClassFormation.DegreeData (Ω ≃ₐ[K] Ω) := by
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  exact
    { degree := absoluteConstantDegree (algebraicClosure k K) K Ω
      degree_surjective := absoluteConstantDegree_surjective (algebraicClosure k K) K Ω
        (separableConstants_fullConstants k K) }

/-- The inertia subgroup of the concrete degree datum fixes the actual maximal
constant extension inside the chosen separable closure. -/
theorem fullConstantDegreeData_inertia :
    (fullConstantDegreeData k K Ω).inertia.toSubgroup =
      (IntermediateField.adjoin K
        (separableClosure (algebraicClosure k K) Ω : Set Ω)).fixingSubgroup := by
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  exact absoluteConstantDegree_ker (algebraicClosure k K) K Ω

end FunctionField

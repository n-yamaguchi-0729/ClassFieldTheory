/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.NormUniqueness

/-!
# Norms from a compositum of finite abelian class fields

The norm group of the actual compositum is the intersection of the two
actual norm groups, as detected by the corresponding fixing subgroups.
-/

noncomputable section

namespace FunctionField

open LocalClassFieldTheory

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]

/-- Norms from the actual abelian compositum are precisely the common norms. -/
theorem finiteAbelian_norm_range_sup
    (E F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E]
    [FiniteDimensional K F] [IsAbelianGalois K F] :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    (IdeleClassGroup.norm (k := k) (K := K) (L := ↥(E ⊔ F))).range =
      (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range ⊓
        (IdeleClassGroup.norm (k := k) (K := K) (L := F)).range := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  rw [← absoluteArtin_comap_restrictionKernel k K (E ⊔ F),
    ← absoluteArtin_comap_restrictionKernel k K E,
    ← absoluteArtin_comap_restrictionKernel k K F, ← Subgroup.comap_inf]
  apply congrArg (fun H : Subgroup (localAbsoluteAbelianProfinite K) =>
    H.comap (absoluteArtin k K).toMonoidHom)
  apply Subgroup.ext
  intro x
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
  change absoluteAbelianRestriction K (E ⊔ F) (QuotientGroup.mk σ) = 1 ↔
    absoluteAbelianRestriction K E (QuotientGroup.mk σ) = 1 ∧
      absoluteAbelianRestriction K F (QuotientGroup.mk σ) = 1
  rw [absoluteAbelianRestriction_mk, absoluteAbelianRestriction_mk,
    absoluteAbelianRestriction_mk]
  change σ ∈ (AlgEquiv.restrictNormalHom ↥(E ⊔ F)).ker ↔
    σ ∈ (AlgEquiv.restrictNormalHom E).ker ∧ σ ∈ (AlgEquiv.restrictNormalHom F).ker
  rw [IntermediateField.restrictNormalHom_ker, IntermediateField.restrictNormalHom_ker,
    IntermediateField.restrictNormalHom_ker, IntermediateField.fixingSubgroup_sup]
  rfl

end FunctionField

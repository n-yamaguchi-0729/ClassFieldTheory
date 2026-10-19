/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.NormUniqueness

/-!
# Class fields inside a given finite abelian extension

Every subgroup containing the norm group of a given finite abelian
extension is realized by an actual intermediate field of that extension.
This finite correspondence does not assert cofinality of norm groups
among all open finite-index subgroups of the usual idele-class group.
-/

noncomputable section

namespace FunctionField

open LocalClassFieldTheory
open scoped IsMulCommutative

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]

/-- Subgroups above a given actual abelian norm group have actual class fields below it. -/
theorem exists_subextension_norm_eq
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] (U : Subgroup (IdeleClassGroup k K)) :
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
    (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range ≤ U →
      ∃ (F : IntermediateField K (SeparableClosure K)) (_ : FiniteDimensional K F)
        (_ : IsAbelianGalois K F), F ≤ E ∧
          (IdeleClassGroup.norm (k := k) (K := K) (L := F)).range = U := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ hU
  let a := abelianFiniteArtin k K E
  let r := absoluteAbelianRestriction K E
  let H := U.map a
  let N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K) :=
    { toOpenSubgroup :=
        { toSubgroup := H.comap r.toMonoidHom
          isOpen' := (isOpen_discrete (H : Set Gal(E/K))).preimage r.continuous_toFun }
      isNormal' := inferInstance }
  let F := absoluteFiniteQuotientField K N
  have hN : absoluteAbelianRestrictionKernel K E ≤ N := by
    intro x hx
    change r x ∈ H
    change r x = 1 at hx
    rw [hx]
    exact H.one_mem
  have hFE : F ≤ E := by
    have hi := absoluteFiniteQuotientField_antitone hN
    rw [absoluteFiniteQuotientField_restrictionKernel] at hi
    exact hi
  refine ⟨F, inferInstance, inferInstance, hFE, ?_⟩
  rw [← absoluteArtin_comap_openNormal k K N]
  have hker : a.ker ≤ U := by
    rw [abelianFiniteArtin_ker]
    exact hU
  have hcomap : H.comap a = U := by
    rw [Subgroup.comap_map_eq, sup_eq_left.mpr hker]
  apply Subgroup.ext
  intro c
  change r (absoluteArtin k K c) ∈ H ↔ c ∈ U
  change absoluteAbelianRestriction K E (absoluteArtin k K c) ∈ H ↔ c ∈ U
  rw [absoluteArtin_restriction]
  exact SetLike.ext_iff.mp hcomap c

end FunctionField

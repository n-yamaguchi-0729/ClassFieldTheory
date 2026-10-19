/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteRestriction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionIntermediate
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteFiniteQuotientTransitions

/-!
# Finite coordinates of absolute function-field reciprocity

Every open finite quotient of the absolute topological abelianization is
an actual finite abelian Galois group. Its Artin map is continuous and
surjective, and the coordinates commute with the quotient transitions.
-/

noncomputable section

namespace FunctionField

open LocalClassFieldTheory CategoryTheory

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]

/-- The continuous Artin coordinate at a finite quotient of the absolute abelianization. -/
def absoluteFiniteArtinCoordinate
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    IdeleClassGroup k K →ₜ* ((localAbsoluteAbelianProfinite K).diagram.obj N : Type) := by
  let akΩ : Algebra k (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
  let aRΩ : Algebra (RatFunc k) (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
  have hkKΩ : IsScalarTower k K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRKΩ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRΩ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
      (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
  let E := absoluteFiniteQuotientField K N
  let f : Gal(E/K) →ₜ* ((localAbsoluteAbelianProfinite K).diagram.obj N : Type) :=
    { toMonoidHom := (absoluteFiniteQuotientEquiv K N).symm.toMulEquiv.toMonoidHom
      continuous_toFun := continuous_of_discreteTopology }
  exact f.comp
    { toMonoidHom := abelianFiniteArtin k K E
      continuous_toFun := continuous_abelianFiniteArtin k K E }

/-- Each finite coordinate is onto its actual finite Galois quotient. -/
theorem absoluteFiniteArtinCoordinate_surjective
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) :
    Function.Surjective (absoluteFiniteArtinCoordinate k K N) := by
  let akΩ : Algebra k (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
  let aRΩ : Algebra (RatFunc k) (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
  have hkKΩ : IsScalarTower k K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRKΩ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRΩ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
      (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
  exact (absoluteFiniteQuotientEquiv K N).symm.surjective.comp
    (abelianFiniteArtin_surjective k K (absoluteFiniteQuotientField K N))

/-- A coordinate vanishes exactly on the actual norm subgroup of its finite fixed field. -/
theorem absoluteFiniteArtinCoordinate_eq_one_iff_mem_norm
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)) (c : IdeleClassGroup k K) :
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
    absoluteFiniteArtinCoordinate k K N c = 1 ↔
      c ∈ (IdeleClassGroup.norm (k := k) (K := K)
        (L := absoluteFiniteQuotientField K N)).range := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  change (absoluteFiniteQuotientEquiv K N).symm
    (abelianFiniteArtin k K (absoluteFiniteQuotientField K N) c) = 1 ↔ _
  exact (map_eq_one_iff _ (absoluteFiniteQuotientEquiv K N).symm.injective).trans
    (abelianFiniteArtin_eq_one_iff_mem_norm k K (absoluteFiniteQuotientField K N) c)

/-- Actual finite Artin coordinates commute with all finite quotient transitions. -/
theorem absoluteFiniteArtinCoordinate_transition
    {N M : OpenNormalSubgroup (localAbsoluteAbelianProfinite K)} (hNM : N ≤ M)
    (c : IdeleClassGroup k K) :
    (localAbsoluteAbelianProfinite K).diagram.map hNM.hom
        (absoluteFiniteArtinCoordinate k K N c) = absoluteFiniteArtinCoordinate k K M c := by
  let akΩ : Algebra k (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
  let aRΩ : Algebra (RatFunc k) (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
  have hkKΩ : IsScalarTower k K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRKΩ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRΩ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
      (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
  let E := absoluteFiniteQuotientField K M
  let F := absoluteFiniteQuotientField K N
  let hEF := absoluteFiniteQuotientField_antitone hNM
  let aEF : Algebra E F := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  have hKEF : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  apply (absoluteFiniteQuotientEquiv K M).injective
  change absoluteFiniteQuotientEquiv K M
      (absoluteFiniteQuotientTransition hNM
        ((absoluteFiniteQuotientEquiv K N).symm (abelianFiniteArtin k K F c))) =
    absoluteFiniteQuotientEquiv K M
      ((absoluteFiniteQuotientEquiv K M).symm (abelianFiniteArtin k K E c))
  rw [ContinuousMulEquiv.apply_symm_apply]
  have ht := DFunLike.congr_fun (absoluteFiniteQuotientEquiv_transition (K := K) hNM)
    ((absoluteFiniteQuotientEquiv K N).symm (abelianFiniteArtin k K F c))
  change intermediateFieldRestrictContinuous K E F hEF
      (absoluteFiniteQuotientEquiv K N
        ((absoluteFiniteQuotientEquiv K N).symm (abelianFiniteArtin k K F c))) =
    absoluteFiniteQuotientEquiv K M
      (absoluteFiniteQuotientTransition hNM
        ((absoluteFiniteQuotientEquiv K N).symm (abelianFiniteArtin k K F c))) at ht
  rw [ContinuousMulEquiv.apply_symm_apply] at ht
  rw [← ht]
  exact abelianFiniteArtin_restrictNormal k K E F c

end FunctionField

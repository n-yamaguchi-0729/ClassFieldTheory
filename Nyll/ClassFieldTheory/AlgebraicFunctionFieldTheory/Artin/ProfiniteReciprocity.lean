/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.CompletedArtin
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteRestriction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteAbelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.NormCofinality
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.FiniteAbelianQuotientKernels
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteCompletionCriteria

/-!
# Profinite function-field reciprocity for the ordinary topology

Actual finite norm cofinality supplies the arithmetic input to the common
completion criterion. Thus the extension of absolute reciprocity is an
isomorphism from the completion for all ordinary open finite quotients.
-/

noncomputable section

namespace FunctionField

open LocalClassFieldTheory

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]

/-- Actual finite abelian norm groups make the finite absolute Artin
quotients cofinal among all ordinary open finite-index quotients. -/
theorem absoluteArtin_preimage_cofinal
    (H : OpenFiniteIndexNormalSubgroup (IdeleClassGroup k K)) :
    ∃ N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K),
      topologicalProfiniteCompletionPreimageIndex
        (localAbsoluteAbelianProfinite K) (absoluteArtin k K) N ≤ H := by
  let akSep : Algebra k (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
  let aRSep : Algebra (RatFunc k) (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
  have hkKSep : IsScalarTower k K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRKSep : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRSep : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
      (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
  have hHfinite : H.toOpenNormalSubgroup.toSubgroup.FiniteIndex := H.finiteIndex'
  obtain ⟨E, hEabelian, hEnorm⟩ :=
    exists_finiteAbelian_norm_le_of_open k K (SeparableClosure K)
      H.toOpenNormalSubgroup.toSubgroup H.toOpenNormalSubgroup.isOpen'
  have hEprincipal : AlgebraicCurve.HasPrincipalDivisors k E :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K E).toHasPrincipalDivisors
  refine ⟨absoluteAbelianRestrictionKernel K E.toIntermediateField, ?_⟩
  intro c hc
  apply hEnorm
  apply (abelianFiniteArtin_eq_one_iff_mem_norm k K E c).mp
  have hrestriction :
      absoluteAbelianRestriction K E.toIntermediateField (absoluteArtin k K c) = 1 :=
    (mem_absoluteAbelianRestrictionKernel_iff K E.toIntermediateField
      (absoluteArtin k K c)).mp hc
  rw [absoluteArtin_restriction k K E.toIntermediateField c] at hrestriction
  exact hrestriction

/-- The completed Artin map is injective for the ordinary idele-class topology. -/
theorem completedArtin_injective : Function.Injective (completedArtin k K) :=
  topologicalProfiniteCompletionLift_injective_of_preimage_cofinal
    (localAbsoluteAbelianProfinite K) (absoluteArtin k K) (absoluteArtin_preimage_cofinal k K)

/-- Global function-field reciprocity identifies the ordinary topological
profinite completion with the actual absolute abelian Galois group. -/
def profiniteReciprocity :
    TopologicalProfiniteCompletion (IdeleClassGroup k K) ≃ₜ*
      localAbsoluteAbelianProfinite K :=
  { Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofBijective (completedArtin k K)
        ⟨completedArtin_injective k K, completedArtin_surjective k K⟩)
      (completedArtin k K).continuous_toFun with
    map_mul' := (completedArtin k K).map_mul }

/-- The profinite isomorphism extends the actual absolute Artin map. -/
theorem profiniteReciprocity_map (c : IdeleClassGroup k K) :
    profiniteReciprocity k K
      (topologicalProfiniteCompletionMap (IdeleClassGroup k K) c) = absoluteArtin k K c :=
  completedArtin_map k K c

end FunctionField

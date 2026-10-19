/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteArtin
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteCompletion
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteCompletionCriteria

/-!
# Reciprocity on the completion for the usual idele-class topology

The existing completion by open finite-index normal subgroups extends the
continuous absolute Artin map. Its dense image makes the extension surjective.
Each finite coordinate is the extension of the actual finite Artin coordinate.
Injectivity requires the arithmetic existence theorem and is not asserted here.
-/

noncomputable section

namespace FunctionField

open LocalClassFieldTheory

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]

/-- Absolute reciprocity extended to the completion by the open finite
quotients of the usual idele-class topology. -/
def completedArtin :
    TopologicalProfiniteCompletion (IdeleClassGroup k K) →ₜ*
      localAbsoluteAbelianProfinite K :=
  topologicalProfiniteCompletionLift (localAbsoluteAbelianProfinite K) (absoluteArtin k K)

/-- On actual idele classes, completed reciprocity is the absolute Artin map. -/
theorem completedArtin_map (c : IdeleClassGroup k K) :
    completedArtin k K (topologicalProfiniteCompletionMap (IdeleClassGroup k K) c) =
      absoluteArtin k K c :=
  topologicalProfiniteCompletionLift_map
    (localAbsoluteAbelianProfinite K) (absoluteArtin k K) c

/-- The completed Artin map is onto the actual absolute abelian Galois group. -/
theorem completedArtin_surjective : Function.Surjective (completedArtin k K) :=
  topologicalProfiniteCompletionLift_surjective_of_denseRange
    (localAbsoluteAbelianProfinite K) (absoluteArtin k K) (absoluteArtin_denseRange k K)

/-- Each finite quotient of completed reciprocity is the canonical continuous
extension of its actual finite Artin coordinate. -/
theorem completedArtin_finiteProjection
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K))
    (x : TopologicalProfiniteCompletion (IdeleClassGroup k K)) :
    (QuotientGroup.mk (completedArtin k K x) :
        localAbsoluteAbelianProfinite K ⧸ N.toSubgroup) =
      topologicalProfiniteCompletionLift
        ((localAbsoluteAbelianProfinite K).diagram.obj N)
        (absoluteFiniteArtinCoordinate k K N) x := by
  let q : localAbsoluteAbelianProfinite K →ₜ*
      ((localAbsoluteAbelianProfinite K).diagram.obj N : Type) :=
    { toMonoidHom := QuotientGroup.mk' N.toSubgroup
      continuous_toFun := (continuous_apply N).comp
        (continuous_subtype_val.comp (ProfiniteGrp.toLimitFun_continuous
          (localAbsoluteAbelianProfinite K))) }
  have heq := (topologicalProfiniteCompletionMap_denseRange (IdeleClassGroup k K)).equalizer
    (q.continuous.comp (completedArtin k K).continuous)
    (topologicalProfiniteCompletionLift
      ((localAbsoluteAbelianProfinite K).diagram.obj N)
      (absoluteFiniteArtinCoordinate k K N)).continuous
    (show (fun c => q (completedArtin k K
        (topologicalProfiniteCompletionMap (IdeleClassGroup k K) c))) =
      (fun c => topologicalProfiniteCompletionLift
        ((localAbsoluteAbelianProfinite K).diagram.obj N)
        (absoluteFiniteArtinCoordinate k K N)
        (topologicalProfiniteCompletionMap (IdeleClassGroup k K) c)) from by
      funext c
      rw [completedArtin_map, topologicalProfiniteCompletionLift_map]
      exact absoluteArtin_finiteProjection k K N c)
  exact congrFun heq x

end FunctionField

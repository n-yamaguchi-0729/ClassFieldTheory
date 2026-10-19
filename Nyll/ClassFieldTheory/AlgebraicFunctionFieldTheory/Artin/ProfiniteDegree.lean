/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.ProfiniteReciprocity
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteConstantDegree
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.NormalizedDegree
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteCompletion

/-!
# Finite coordinates and constant degree of completed reciprocity

Extend the actual integer normalized degree independently to the ordinary
profinite completion. Density identifies it with arithmetic constant degree
after the reciprocity isomorphism. The finite-coordinate formulas remain
the canonical extensions of the actual finite Artin maps.
-/

noncomputable section
namespace FunctionField

open ClassFormation LocalClassFieldTheory

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]

/-- Normalized integer idele degree embedded continuously in the profinite integers. -/
def normalizedDegreeToProfinite : IdeleClassGroup k K →ₜ* ZHatMul :=
  { toMonoidHom := (Int.castRingHom ZHat).toAddMonoidHom.toMultiplicative.comp
      (IdeleClassGroup.normalizedDegree (k := k) (K := K))
    continuous_toFun := (continuous_of_discreteTopology :
      Continuous (fun z : Multiplicative ℤ => Multiplicative.ofAdd (z.toAdd : ZHat))).comp
        (IdeleClassGroup.continuous_normalizedDegree (k := k) (K := K)) }

/-- The extension of actual normalized degree to the ordinary profinite completion. -/
def completedNormalizedDegree :
    TopologicalProfiniteCompletion (IdeleClassGroup k K) →ₜ* ZHatMul :=
  topologicalProfiniteCompletionLift (ProfiniteGrp.of ZHatMul) (normalizedDegreeToProfinite k K)

/-- Completed reciprocity has the arithmetic full-constant degree obtained
by independently completing the normalized integer idele degree. -/
theorem profiniteReciprocity_constantDegree
    (x : TopologicalProfiniteCompletion (IdeleClassGroup k K)) :
    absoluteAbelianDegree k K (profiniteReciprocity k K x) = completedNormalizedDegree k K x := by
  have hleft : Continuous (fun y => absoluteAbelianDegree k K (profiniteReciprocity k K y)) :=
    (absoluteAbelianDegree k K).continuous_toFun.comp (profiniteReciprocity k K).continuous
  have heq := (topologicalProfiniteCompletionMap_denseRange (IdeleClassGroup k K)).equalizer
    hleft (completedNormalizedDegree k K).continuous_toFun (show
      (fun c => absoluteAbelianDegree k K (profiniteReciprocity k K
        (topologicalProfiniteCompletionMap (IdeleClassGroup k K) c))) =
      (fun c => completedNormalizedDegree k K
        (topologicalProfiniteCompletionMap (IdeleClassGroup k K) c)) from by
        funext c
        rw [profiniteReciprocity_map, absoluteAbelianDegree_artin]
        exact (topologicalProfiniteCompletionLift_map
          (ProfiniteGrp.of ZHatMul) (normalizedDegreeToProfinite k K) c).symm)
  exact congrFun heq x

/-- Every finite coordinate of the reciprocity isomorphism is the
canonical extension of the actual finite Artin coordinate. -/
theorem profiniteReciprocity_finiteProjection
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K))
    (x : TopologicalProfiniteCompletion (IdeleClassGroup k K)) :
    (QuotientGroup.mk (profiniteReciprocity k K x) :
        localAbsoluteAbelianProfinite K ⧸ N.toSubgroup) =
      topologicalProfiniteCompletionLift
        ((localAbsoluteAbelianProfinite K).diagram.obj N)
        (absoluteFiniteArtinCoordinate k K N) x :=
  completedArtin_finiteProjection k K N x

end FunctionField

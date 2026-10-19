/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Definitions.FunctionField.ClassField
import Nyll.ClassFieldTheory.Definitions.FunctionField.FiniteArtin
import Nyll.ClassFieldTheory.Definitions.FunctionField.ProfiniteReciprocity
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteArtin
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteRestriction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.ProfiniteReciprocity
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.ProfiniteDegree
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteCompletion

/-!
# The dense absolute Artin map and its profinite extension

The public absolute map has dense range, restricts to finite Artin
reciprocity, and is the restriction of the topological profinite
reciprocity isomorphism along the canonical completion map.
-/

noncomputable section

namespace ClassFieldTheory.FunctionField

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [_root_.FunctionField k K]

/-- Absolute reciprocity has dense image in the actual abelian Galois group. -/
theorem absoluteArtin_denseRange : DenseRange (absoluteArtin k K) := by
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  exact _root_.FunctionField.absoluteArtin_denseRange k K

/-- Restriction to every finite abelian subextension recovers the public
finite Artin map. The upper field's principal divisors are supplied internally. -/
theorem absoluteArtin_restriction :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
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
    ∀ (E : FiniteAbelianExtension K) (c : _root_.FunctionField.IdeleClassGroup k K),
      LocalClassFieldTheory.absoluteAbelianRestriction K E.val (absoluteArtin k K c) =
        finiteArtin k K E.val c := by
  intro hK akΩ aRΩ hkKΩ hRKΩ hkRΩ E c
  exact _root_.FunctionField.absoluteArtin_restriction k K E.val c

/-- The topological profinite isomorphism extends actual absolute reciprocity. -/
theorem profiniteReciprocity_map :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    ∀ c : _root_.FunctionField.IdeleClassGroup k K,
      profiniteReciprocity k K (ideleClassCompletionMap k K c) = absoluteArtin k K c := by
  intro hK c
  exact _root_.FunctionField.profiniteReciprocity_map k K c

/-- The completed degree agrees with actual normalized integer idele degree
on the dense canonical image. -/
theorem completedNormalizedDegree_map :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    ∀ c : _root_.FunctionField.IdeleClassGroup k K,
      completedNormalizedDegree k K (ideleClassCompletionMap k K c) =
        Multiplicative.ofAdd
          ((_root_.FunctionField.IdeleClassGroup.normalizedDegree (k := k) (K := K) c).toAdd :
            ClassFormation.ZHat) := by
  intro hK c
  exact LocalClassFieldTheory.topologicalProfiniteCompletionLift_map
    (ProfiniteGrp.of ClassFormation.ZHatMul)
    (_root_.FunctionField.normalizedDegreeToProfinite k K) c

/-- Profinite reciprocity identifies arithmetic constant Frobenius degree
with the independent completion of normalized integer idele degree. -/
theorem profiniteReciprocity_constantDegree (x : IdeleClassProfiniteCompletion k K) :
    absoluteAbelianDegree k K (profiniteReciprocity k K x) = completedNormalizedDegree k K x := by
  have hK : AlgebraicCurve.HasPrincipalDivisors k K :=
    (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
  exact _root_.FunctionField.profiniteReciprocity_constantDegree k K x

/-- Each finite coordinate is the canonical continuous extension of the
actual finite Artin coordinate. -/
theorem profiniteReciprocity_finiteProjection
    (N : OpenNormalSubgroup (AbsoluteAbelianGaloisGroup K))
    (x : IdeleClassProfiniteCompletion k K) :
    let _ : AlgebraicCurve.HasPrincipalDivisors k K :=
      (_root_.FunctionField.isCurveOver k K).toHasPrincipalDivisors
    (QuotientGroup.mk (profiniteReciprocity k K x) :
        AbsoluteAbelianGaloisGroup K ⧸ N.toSubgroup) =
      LocalClassFieldTheory.topologicalProfiniteCompletionLift
        ((AbsoluteAbelianGaloisGroup K).diagram.obj N)
        (_root_.FunctionField.absoluteFiniteArtinCoordinate k K N) x := by
  intro hK
  exact _root_.FunctionField.profiniteReciprocity_finiteProjection k K N x

end ClassFieldTheory.FunctionField

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Algebra.RestrictedProduct.ValuationTopology
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Topology
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.PrincipalTopology
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.CompactUnits
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Continuous degree and the degree-zero idele classes

Local orders give a continuous map to discrete divisors. The degree map is
therefore continuous, and it descends continuously to the idele class group.
Its degree-zero subgroup is both open and closed.
-/

noncomputable section

namespace FunctionField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace IdeleGroup

/-- The idele degree is continuous with values in the discrete integers. -/
theorem continuous_degree : Continuous (degree (k := k) (K := K)) := by
  let : TopologicalSpace (Multiplicative (AlgebraicCurve.Divisor k K)) := ⊥
  have : DiscreteTopology (Multiplicative (AlgebraicCurve.Divisor k K)) := ⟨rfl⟩
  have hdiv : Continuous (divisor (k := k) (K := K)) :=
    RestrictedProduct.DiscreteValuation.continuous_valuationVector
      (fun v : AlgebraicCurve.Place k K => v.adicCompletion)
  exact (continuous_of_discreteTopology :
    Continuous AlgebraicCurve.Divisor.degree.toMultiplicative).comp hdiv

end IdeleGroup

namespace IdeleClassGroup

variable [AlgebraicCurve.HasPrincipalDivisors k K]

/-- The descended degree respects the quotient topology on idele classes. -/
theorem continuous_degree : Continuous (degree (k := k) (K := K)) := by
  apply continuous_coinduced_dom.2
  exact IdeleGroup.continuous_degree

/-- Degree-zero idele classes form an open subgroup. -/
theorem isOpen_degreeZero :
    IsOpen (degreeZero (k := k) (K := K) : Set (IdeleClassGroup k K)) := by
  change IsOpen ((degree (k := k) (K := K)) ⁻¹' {1})
  exact (isOpen_discrete {1}).preimage continuous_degree

/-- Degree-zero idele classes form a closed subgroup. -/
theorem isClosed_degreeZero :
    IsClosed (degreeZero (k := k) (K := K) : Set (IdeleClassGroup k K)) := by
  change IsClosed ((degree (k := k) (K := K)) ⁻¹' {1})
  exact isClosed_singleton.preimage continuous_degree

/-- The quotient by principal ideles is Hausdorff because that subgroup is closed. -/
theorem t2Space [PerfectField k] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K] :
    T2Space (IdeleClassGroup k K) := by
  have : IsClosed (IdeleGroup.principalSubgroup k K : Set (IdeleGroup k K)) :=
    IdeleGroup.principalSubgroup_isClosed
  have : T3Space (IdeleClassGroup k K) :=
    QuotientGroup.instT3Space (IdeleGroup.principalSubgroup k K)
  exact T25Space.t2Space

/-- The idele class group of a finite-constant-field function field is locally compact. -/
theorem locallyCompactSpace [Finite k] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K] :
    LocallyCompactSpace (IdeleClassGroup k K) := by
  have : LocallyCompactSpace (IdeleGroup k K) := IdeleGroup.locallyCompactSpace
  infer_instance

end IdeleClassGroup

end FunctionField

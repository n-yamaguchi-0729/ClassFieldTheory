/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Constants
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Degree
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Divisor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.IdeleConstantExtension
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Topology
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChange
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormDivisor

/-!
# Idele-class degree normalized by the full constants

Every class degree is divisible by the degree of the actual relative algebraic
closure of the base constants. Division by this proved factor defines a
continuous homomorphism with the same degree-zero kernel. It agrees with the
degree after the existing equivalence that enlarges constants, and records the
constant-field factors in finite-extension norm and inclusion formulas.

No surjectivity onto the integers or Frobenius comparison is assumed here.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]

/-- Degree with the full-constant-field factor removed. -/
def normalizedDegree : IdeleClassGroup k K →* Multiplicative ℤ where
  toFun c := Multiplicative.ofAdd
    ((degree (k := k) (K := K) c).toAdd / Module.finrank k (algebraicClosure k K))
  map_one' := by
    apply Multiplicative.ext
    change (degree (k := k) (K := K) 1).toAdd / _ = 0
    rw [map_one]
    exact Int.zero_ediv _
  map_mul' c d := by
    apply Multiplicative.ext
    change (degree (k := k) (K := K) (c * d)).toAdd / _ = _ + _
    rw [map_mul, toAdd_mul]
    exact Int.add_ediv_of_dvd_left (fullConstants_degree_dvd c)

/-- Multiplying the normalized degree recovers the original integer degree. -/
theorem fullConstants_mul_normalizedDegree (c : IdeleClassGroup k K) :
    (Module.finrank k (algebraicClosure k K) : ℤ) *
      (normalizedDegree (k := k) (K := K) c).toAdd =
        (degree (k := k) (K := K) c).toAdd :=
  Int.mul_ediv_cancel_of_dvd (fullConstants_degree_dvd c)

/-- Normalizing degree is continuous for the quotient topology and discrete integers. -/
theorem continuous_normalizedDegree :
    Continuous (normalizedDegree (k := k) (K := K)) :=
  (continuous_of_discreteTopology : Continuous (fun n : Multiplicative ℤ =>
    Multiplicative.ofAdd (n.toAdd / Module.finrank k (algebraicClosure k K)))).comp
      continuous_degree

/-- Normalization preserves exactly the degree-zero subgroup. -/
theorem normalizedDegree_eq_one_iff (c : IdeleClassGroup k K) :
    normalizedDegree (k := k) (K := K) c = 1 ↔ degree (k := k) (K := K) c = 1 := by
  constructor
  · intro h
    apply Multiplicative.ext
    change (degree (k := k) (K := K) c).toAdd = 0
    rw [← fullConstants_mul_normalizedDegree c, h]
    exact mul_zero _
  · intro h
    apply Multiplicative.ext
    change (degree (k := k) (K := K) c).toAdd / _ = 0
    rw [h]
    exact Int.zero_ediv _

theorem normalizedDegree_ker :
    (normalizedDegree (k := k) (K := K)).ker = degreeZero (k := k) (K := K) := by
  apply Subgroup.ext
  intro c
  exact normalizedDegree_eq_one_iff c

section Presentation

variable [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- The integer quotient is the actual degree computed over the full constants. -/
theorem normalizedDegree_eq_degree_constantEquiv
    [AlgebraicCurve.HasPrincipalDivisors (algebraicClosure k K) K]
    (c : IdeleClassGroup k K) :
    normalizedDegree (k := k) (K := K) c =
      degree (k := algebraicClosure k K) (K := K)
        (constantEquiv k (algebraicClosure k K) K c) := by
  apply Multiplicative.ext
  change (degree (k := k) (K := K) c).toAdd / _ = _
  rw [degree_constantEquiv k (algebraicClosure k K) K c]
  exact Int.mul_ediv_cancel_left _
    (Int.natCast_ne_zero.mpr (FunctionField.fullConstants_degree_pos k K).ne')

/-- A one-place idele has normalized degree equal to its local order times
the degree of the place over the full constant field. -/
theorem normalizedDegree_placeIdele
    (v : AlgebraicCurve.Place k K) (x : v.adicCompletionˣ) :
    (normalizedDegree (k := k) (K := K)
      (mk (k := k) (K := K) (IdeleGroup.placeIdele v x))).toAdd =
      (IdeleGroup.localOrder v x).toAdd *
        (v.extendConstants (algebraicClosure k K)).deg := by
  change (degree (k := k) (K := K)
    (mk (k := k) (K := K) (IdeleGroup.placeIdele v x))).toAdd /
      (Module.finrank k (algebraicClosure k K) : ℤ) = _
  rw [degree_mk, IdeleGroup.degree_placeIdele]
  have hv : v.deg = Module.finrank k (algebraicClosure k K) *
      (v.extendConstants (algebraicClosure k K)).deg :=
    AlgebraicCurve.Place.deg_forgetConstants (K := k)
      (v.extendConstants (algebraicClosure k K))
  rw [hv, Nat.cast_mul, mul_left_comm]
  exact Int.mul_ediv_cancel_left _
    (Int.natCast_ne_zero.mpr (FunctionField.fullConstants_degree_pos k K).ne')

/-- The normalized degree has a positive value without requiring a rational place. -/
theorem exists_positive_normalizedDegree [Finite k] :
    ∃ c : IdeleClassGroup k K, 0 < (normalizedDegree (k := k) (K := K) c).toAdd := by
  obtain ⟨c, hc⟩ := exists_positive_degree (k := k) (K := K)
  exact ⟨c, Int.ediv_pos_of_pos_of_dvd hc (Int.natCast_nonneg _)
    (fullConstants_degree_dvd c)⟩

end Presentation

section Extension

variable {L : Type*} [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [AlgebraicCurve.HasPrincipalDivisors k L]

/-- Norm preserves base-field degree, retaining both full-constant normalization factors. -/
theorem fullConstants_mul_normalizedDegree_norm (c : IdeleClassGroup k L) :
    (Module.finrank k (algebraicClosure k K) : ℤ) *
        (normalizedDegree (k := k) (K := K) (norm (K := K) (L := L) c)).toAdd =
      (Module.finrank k (algebraicClosure k L) : ℤ) *
        (normalizedDegree (k := k) (K := L) c).toAdd := by
  rw [fullConstants_mul_normalizedDegree, fullConstants_mul_normalizedDegree, degree_norm]

/-- Inclusion scales base-field degree by the actual extension degree. -/
theorem fullConstants_mul_normalizedDegree_baseChange (c : IdeleClassGroup k K) :
    (Module.finrank k (algebraicClosure k L) : ℤ) *
        (normalizedDegree (k := k) (K := L) (baseChange (K := K) (L := L) c)).toAdd =
      (Module.finrank K L : ℤ) * (Module.finrank k (algebraicClosure k K) : ℤ) *
        (normalizedDegree (k := k) (K := K) c).toAdd := by
  rw [fullConstants_mul_normalizedDegree, mul_assoc, fullConstants_mul_normalizedDegree]
  exact degree_baseChange c

end Extension

end FunctionField.IdeleClassGroup

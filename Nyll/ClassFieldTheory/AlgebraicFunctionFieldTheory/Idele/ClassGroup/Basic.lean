/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.PrincipalCore
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Divisor classes and the degree of an idele class

The divisor-class map is constructed from the actual all-place divisor map.
Its descent and that of degree use the proved comparison with principal divisors.
No finiteness is asserted for the full divisor or idele class group.
-/

noncomputable section

namespace FunctionField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace IdeleGroup

/-- The divisor class represented by an idele. -/
def divisorClass : IdeleGroup k K →* Multiplicative (AlgebraicCurve.Pic k K) :=
  (QuotientAddGroup.mk' AlgebraicCurve.Divisor.principal).toMultiplicative.comp divisor

/-- Triviality of the divisor class means that its actual divisor is principal. -/
theorem divisorClass_eq_one_iff (a : IdeleGroup k K) :
    divisorClass (k := k) (K := K) a = 1 ↔
      AlgebraicCurve.Divisor.IsPrincipal (divisor (k := k) (K := K) a).toAdd := by
  change (QuotientAddGroup.mk (divisor (k := k) (K := K) a).toAdd :
    AlgebraicCurve.Pic k K) = 0 ↔ _
  exact QuotientAddGroup.eq_zero_iff _

/-- Every divisor class has an idele representative. -/
theorem divisorClass_surjective :
    Function.Surjective (divisorClass (k := k) (K := K)) := by
  intro c
  obtain ⟨D, hD⟩ := QuotientAddGroup.mk_surjective c.toAdd
  obtain ⟨a, ha⟩ := divisor_surjective (k := k) (K := K) (Multiplicative.ofAdd D)
  refine ⟨a, ?_⟩
  apply Multiplicative.ext
  change QuotientAddGroup.mk (divisor (k := k) (K := K) a).toAdd = c.toAdd
  rw [ha]
  exact hD

variable [AlgebraicCurve.HasPrincipalDivisors k K]

@[simp]
theorem divisorClass_principalIdele (x : Kˣ) :
    divisorClass (k := k) (K := K) (principalIdele k K x) = 1 :=
  (divisorClass_eq_one_iff _).2
    ⟨(x : K), x.ne_zero, fun v => divisor_principalIdele_apply x v⟩

/-- A trivial divisor class can be represented by an idele integral at every place
after division by one principal idele. -/
theorem divisorClass_eq_one_iff_exists_integral (a : IdeleGroup k K) :
    divisorClass (k := k) (K := K) a = 1 ↔ ∃ x : Kˣ, ∀ v : AlgebraicCurve.Place k K,
      (a / principalIdele k K x) v ∈ v.adicCompletionIntegers.units := by
  constructor
  · intro h
    obtain ⟨f, hf, hD⟩ := (divisorClass_eq_one_iff a).1 h
    let x : Kˣ := Units.mk0 f hf
    refine ⟨x, (divisor_eq_one_iff _).1 ?_⟩
    have hd : divisor (k := k) (K := K) a =
        divisor (k := k) (K := K) (principalIdele k K x) := by
      apply Multiplicative.ext
      ext v
      exact (hD v).trans (divisor_principalIdele_apply x v).symm
    rw [map_div, hd, div_self']
  · rintro ⟨x, hx⟩
    have hd := (divisor_eq_one_iff _).2 hx
    rw [map_div, div_eq_one] at hd
    apply (divisorClass_eq_one_iff a).2
    refine ⟨(x : K), x.ne_zero, fun v => ?_⟩
    rw [hd]
    exact divisor_principalIdele_apply x v

end IdeleGroup

namespace IdeleClassGroup

variable [AlgebraicCurve.HasPrincipalDivisors k K]

/-- The canonical projection to the idele class group. -/
def mk : IdeleGroup k K →* IdeleClassGroup k K :=
  QuotientGroup.mk' (IdeleGroup.principalSubgroup k K)

theorem mk_surjective : Function.Surjective (mk (k := k) (K := K)) :=
  QuotientGroup.mk'_surjective _

/-- Divisor classes descend through the subgroup of principal ideles. -/
def divisorClass : IdeleClassGroup k K →* Multiplicative (AlgebraicCurve.Pic k K) :=
  QuotientGroup.lift (IdeleGroup.principalSubgroup k K) IdeleGroup.divisorClass (by
    rintro _ ⟨x, rfl⟩
    exact IdeleGroup.divisorClass_principalIdele x)

@[simp]
theorem divisorClass_mk (a : IdeleGroup k K) :
    divisorClass (k := k) (K := K) (mk (k := k) (K := K) a) =
      IdeleGroup.divisorClass (k := k) (K := K) a :=
  rfl

theorem divisorClass_surjective :
    Function.Surjective (divisorClass (k := k) (K := K)) := by
  intro c
  obtain ⟨a, ha⟩ := IdeleGroup.divisorClass_surjective (k := k) (K := K) c
  exact ⟨mk (k := k) (K := K) a, ha⟩

/-- Degree descends because principal divisors have degree zero. -/
def degree : IdeleClassGroup k K →* Multiplicative ℤ :=
  QuotientGroup.lift (IdeleGroup.principalSubgroup k K) IdeleGroup.degree (by
    rintro _ ⟨x, rfl⟩
    exact IdeleGroup.degree_principalIdele x)

@[simp]
theorem degree_mk (a : IdeleGroup k K) :
    degree (k := k) (K := K) (mk (k := k) (K := K) a) =
      IdeleGroup.degree (k := k) (K := K) a :=
  rfl

/-- The subgroup of idele classes of degree zero. -/
def degreeZero : Subgroup (IdeleClassGroup k K) := degree.ker

theorem mem_degreeZero (c : IdeleClassGroup k K) :
    c ∈ degreeZero (k := k) (K := K) ↔ degree (k := k) (K := K) c = 1 :=
  Iff.rfl

end IdeleClassGroup

end FunctionField

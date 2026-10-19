/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormPicard
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormOpen
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.FixedNormQuotient

/-!
# Actual norm detection on Picard groups in unramified extensions

Unramified completed norms lift every integral unit. Assemble those local
preimages into an actual idele, then remove principal divisors. Consequently
the actual idele-class norm subgroup is the preimage of the actual Picard
norm subgroup under the divisor-class map.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place RestrictedProduct

namespace FunctionField

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]

namespace IdeleGroup

/-- Every everywhere-integral idele is an actual norm in an everywhere-unramified extension. -/
theorem integralSubgroup_le_norm_range_of_unramified
    (he : ∀ w : Place k L, w.ramificationIndex K = 1) :
    integralSubgroup (k := k) (K := K) ≤ (norm (k := k) (K := K) (L := L)).range := by
  classical
  intro a ha
  choose w hw using (fun v : Place k K => Place.exists_restrict_eq (M := L) v)
  have hex (v : Place k K) : ∃ y : (w v).adicCompletionˣ,
      y ∈ (w v).adicCompletionIntegers.units ∧ localNormOver v (w v) (hw v) y = a v :=
    exists_integral_localNormOver_eq_of_ramificationIndex_eq_one
      v (w v) (hw v) (he (w v)) (a v) (ha v)
  choose y hyint hy using hex
  apply mem_norm_range_of_normComponent_preimages a (fun v => placeIdele (w v) (y v))
  · intro v
    exact (normComponent_placeIdele v (w v) (hw v) (y v)).trans (hy v)
  · exact Filter.Eventually.of_forall (fun v =>
      fiberProjection_placeIdele_mem_integral v (w v) (y v) (hyint v))

end IdeleGroup

namespace IdeleClassGroup

/-- A class with trivial divisor class is an actual norm in an unramified extension. -/
theorem ker_divisorClass_le_norm_range_of_unramified
    (he : ∀ w : Place k L, w.ramificationIndex K = 1) :
    (divisorClass (k := k) (K := K)).ker ≤ (norm (k := k) (K := K) (L := L)).range := by
  intro c hc
  obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := K) c
  have ha : IdeleGroup.divisorClass (k := k) (K := K) a = 1 := hc
  obtain ⟨x, hx⟩ := (IdeleGroup.divisorClass_eq_one_iff_exists_integral a).mp ha
  obtain ⟨b, hb⟩ := IdeleGroup.integralSubgroup_le_norm_range_of_unramified he hx
  refine ⟨mk (k := k) (K := L) b, ?_⟩
  change mk (k := k) (K := K) (IdeleGroup.norm (K := K) (L := L) b) =
    mk (k := k) (K := K) a
  rw [hb, map_div]
  have hprincipal : mk (k := k) (K := K) (IdeleGroup.principalIdele k K x) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
  rw [hprincipal, div_one]

/-- Actual Picard norm membership detects actual idele-class norm membership when unramified. -/
theorem mem_norm_range_iff_picard_of_unramified
    (he : ∀ w : Place k L, w.ramificationIndex K = 1) (c : IdeleClassGroup k K) :
    c ∈ (norm (k := k) (K := K) (L := L)).range ↔
      divisorClass (k := k) (K := K) c ∈
        (Pic.norm (k := k) (K := K) (L := L)).toMultiplicative.range := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨divisorClass (k := k) (K := L) b, (divisorClass_norm b).symm⟩
  · rintro ⟨p, hp⟩
    obtain ⟨b, hb⟩ := divisorClass_surjective (k := k) (K := L) p
    have hker : c / norm (k := k) (K := K) (L := L) b ∈
        (divisorClass (k := k) (K := K)).ker := by
      change divisorClass (k := k) (K := K) (c / norm (K := K) (L := L) b) = 1
      rw [map_div, divisorClass_norm, hb, hp, div_self']
    have hd := ker_divisorClass_le_norm_range_of_unramified he hker
    have hn : norm (k := k) (K := K) (L := L) b ∈
        (norm (k := k) (K := K) (L := L)).range := ⟨b, rfl⟩
    simpa only [div_mul_cancel] using
      (norm (k := k) (K := K) (L := L)).range.mul_mem hd hn

/-- In an unramified extension the actual idele-class and Picard norm quotients agree. -/
def normQuotientEquivPicard_of_unramified
    (he : ∀ w : Place k L, w.ramificationIndex K = 1) :
    (IdeleClassGroup k K ⧸ (norm (k := k) (K := K) (L := L)).range) ≃*
      (Multiplicative (Pic k K) ⧸
        (Pic.norm (k := k) (K := K) (L := L)).toMultiplicative.range) := by
  let P := (Pic.norm (k := k) (K := K) (L := L)).toMultiplicative.range
  let d := (QuotientGroup.mk' P).comp (divisorClass (k := k) (K := K))
  have hker : (norm (k := k) (K := K) (L := L)).range = d.ker := by
    ext c
    constructor
    · intro hc
      exact (QuotientGroup.eq_one_iff _).mpr
        ((mem_norm_range_iff_picard_of_unramified he c).mp hc)
    · intro hc
      exact (mem_norm_range_iff_picard_of_unramified he c).mpr
        ((QuotientGroup.eq_one_iff _).mp hc)
  have hsurj : Function.Surjective d :=
    (QuotientGroup.mk'_surjective P).comp (divisorClass_surjective (k := k) (K := K))
  exact (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective d hsurj)

end IdeleClassGroup

end FunctionField

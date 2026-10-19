/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Genus.AdelicGenus
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.FiniteDimensionalLSpaceZero
import Nyll.GaloisCohomology.ArtinSchreier.RootCharacter
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Artin–Schreier classes with bounded poles

For an effective divisor D, an Artin–Schreier coboundary has poles bounded
by pD exactly when its source has poles bounded by D. Thus the bounded
parameter classes are a concrete finite quotient of Riemann–Roch spaces.
-/

noncomputable section

open AlgebraicCurve
open scoped WithZero

namespace FunctionField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
    (p : ℕ) [Fact p.Prime] [CharP K p]

omit [CharP K p] in
private theorem artinSchreier_mem_lSpace_iff
    (D : Divisor k K) (hD : 0 ≤ D) (b : K) :
    b ^ p - b ∈ LSpace (p • D) ↔ b ∈ LSpace D := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  constructor
  · intro hb v
    by_contra hn
    have hlt : WithZero.exp (D v) < v.adicValuation b := lt_of_not_ge hn
    have hDexp : (1 : ℤᵐ⁰) ≤ WithZero.exp (D v) := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      exact hD v
    have hlarge : 1 < v.adicValuation b := hDexp.trans_lt hlt
    have hpow : v.adicValuation b < v.adicValuation (b ^ p) := by
      rw [map_pow]
      exact lt_self_pow₀ hlarge hp
    have h := hb v
    rw [v.adicValuation.map_sub_eq_of_lt_left hpow, map_pow,
      Finsupp.smul_apply] at h
    have hstrict : WithZero.exp (p • D v) < v.adicValuation b ^ p := by
      rw [WithZero.exp_nsmul]
      exact pow_lt_pow_left₀ hlt zero_le (Nat.ne_zero_of_lt hp)
    exact (not_lt_of_ge h) hstrict
  · intro hb
    have hpD : D ≤ p • D := by
      intro v
      simp only [Finsupp.smul_apply, nsmul_eq_mul]
      have hp' : (1 : ℤ) ≤ p := by exact_mod_cast hp.le
      have hDv : 0 ≤ D v := hD v
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp' hDv
    apply (LSpace (p • D)).sub_mem
    · intro v
      rw [map_pow, Finsupp.smul_apply, WithZero.exp_nsmul]
      exact pow_le_pow_left₀ zero_le (hb v) p
    · exact lSpace_mono hpD hb

/-- The actual image of bounded functions in the additive AS quotient. -/
def boundedArtinSchreierClasses (D : Divisor k K) :
    AddSubgroup (K ⧸ ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range) :=
  (LSpace D).toAddSubgroup.map
    (QuotientAddGroup.mk' ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range)

private def boundedArtinSchreierMap (D : Divisor k K) (hD : 0 ≤ D) :
    LSpace D →+ LSpace (p • D) where
  toFun b := ⟨(b : K) ^ p - b, (artinSchreier_mem_lSpace_iff p D hD b).mpr b.property⟩
  map_zero' := Subtype.ext (by
    change (0 : K) ^ p - 0 = 0
    rw [zero_pow (Fact.out : p.Prime).ne_zero, sub_zero])
  map_add' a b := Subtype.ext (by
    change ((a : K) + b) ^ p - ((a : K) + b) =
      ((a : K) ^ p - a) + ((b : K) ^ p - b)
    rw [add_pow_char]
    ring)

private def boundedArtinSchreierProjection (D : Divisor k K) :
    LSpace D →+ K ⧸ ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range :=
  (QuotientAddGroup.mk' ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range).comp
    (LSpace D).toAddSubgroup.subtype

private theorem boundedArtinSchreierProjection_ker
    (D : Divisor k K) (hD : 0 ≤ D) :
    (boundedArtinSchreierProjection p (p • D)).ker =
      (boundedArtinSchreierMap p D hD).range := by
  apply AddSubgroup.ext
  intro a
  change (a : K ⧸
    ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  constructor
  · rintro ⟨b, hb⟩
    have hbound : b ^ p - b ∈ LSpace (p • D) := by
      change b ^ p - b = (a : K) at hb
      rw [hb]
      exact a.property
    refine ⟨⟨b, (artinSchreier_mem_lSpace_iff p D hD b).mp hbound⟩, ?_⟩
    exact Subtype.ext hb
  · rintro ⟨b, hb⟩
    exact ⟨b, congrArg Subtype.val hb⟩

private def boundedArtinSchreierKernelEquiv
    (D : Divisor k K) (hD : 0 ≤ D) :
    (boundedArtinSchreierMap p D hD).ker ≃ ZMod p := by
  let f : ZMod p → (boundedArtinSchreierMap p D hD).ker := fun z =>
    ⟨⟨(z.val : K), lSpace_mono hD (by
      simpa only [map_natCast] using
        (algebraMap_mem_lSpace_zero (K := k) (F := K) (z.val : k)))⟩, by
      apply Subtype.ext
      change (z.val : K) ^ p - z.val = 0
      have hz := congrArg (ZMod.castHom (dvd_refl p) K) (ZMod.pow_card z)
      simpa only [map_pow, ZMod.castHom_apply, ZMod.cast_eq_val, sub_eq_zero] using hz⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply (ZMod.castHom (dvd_refl p) K).injective
      simpa only [ZMod.castHom_apply, ZMod.cast_eq_val] using
        (congrArg (fun b => ((b.val : LSpace D) : K)) h)
    · intro b
      have hb : ((b.val : LSpace D) : K) ^ p = b.val := by
        have h := congrArg Subtype.val b.property
        exact sub_eq_zero.mp h
      obtain ⟨z, hz⟩ := ArtinSchreierTheory.exists_zmod_of_pow_eq p K hb
      have hz' : (z.val : K) = ((b.val : LSpace D) : K) := by
        simpa only [ZMod.castHom_apply, ZMod.cast_eq_val] using hz
      exact ⟨z, Subtype.ext (Subtype.ext hz')⟩
  exact (Equiv.ofBijective f hf).symm

/-- Bounded parameter classes form a finite group over a finite constant field. -/
theorem boundedArtinSchreierClasses_finite
    [Finite k] [IsCurveOver k K]
    [FiniteDimensional k (LSpace (0 : Divisor k K))] (D : Divisor k K) :
    Finite (boundedArtinSchreierClasses p D) := by
  have hdimension : FiniteDimensional k (LSpace D) := finiteDimensional_lSpace D
  have hfinite : Finite (LSpace D) := Module.finite_of_finite k
  let f : LSpace D → boundedArtinSchreierClasses p D := fun b =>
    ⟨boundedArtinSchreierProjection p D b, ⟨b, b.property, rfl⟩⟩
  apply Finite.of_surjective f
  rintro ⟨a, b, hb, hab⟩
  exact ⟨⟨b, hb⟩, Subtype.ext hab⟩

/-- Counting the actual bounded AS classes uses only the two RR spaces and
the p-element kernel of the Frobenius-minus-identity map. -/
theorem card_boundedArtinSchreierClasses_mul_card_lSpace
    (D : Divisor k K) (hD : 0 ≤ D) :
    Nat.card (boundedArtinSchreierClasses p (p • D)) * Nat.card (LSpace D) =
      Nat.card (LSpace (p • D)) * p := by
  let f := boundedArtinSchreierMap p D hD
  let q := boundedArtinSchreierProjection p (p • D)
  have hker : Nat.card f.ker = p := by
    rw [Nat.card_congr (boundedArtinSchreierKernelEquiv p D hD), Nat.card_eq_fintype_card,
      ZMod.card]
  have hf := f.ker.card_eq_card_quotient_mul_card_addSubgroup
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv, hker] at hf
  have hq := q.ker.card_eq_card_quotient_mul_card_addSubgroup
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange q).toEquiv] at hq
  have hqr : q.range = boundedArtinSchreierClasses p (p • D) := by
    apply AddSubgroup.ext
    intro a
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b, b.property, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩
  have hqker : q.ker = f.range := boundedArtinSchreierProjection_ker p D hD
  rw [hqr, hqker] at hq
  rw [hf, hq, mul_assoc]

/-- Exact cardinality of the bounded AS classes in terms of RR dimensions. -/
theorem card_boundedArtinSchreierClasses
    [Finite k] [IsCurveOver k K]
    [FiniteDimensional k (LSpace (0 : Divisor k K))]
    (D : Divisor k K) (hD : 0 ≤ D) :
    Nat.card (boundedArtinSchreierClasses p (p • D)) =
      p * Nat.card k ^ (ell (p • D) - ell D) := by
  have hfiniteD : FiniteDimensional k (LSpace D) := finiteDimensional_lSpace D
  have hfinitepD : FiniteDimensional k (LSpace (p • D)) := finiteDimensional_lSpace (p • D)
  have hle : D ≤ p • D := by
    intro v
    simp only [Finsupp.smul_apply, nsmul_eq_mul]
    have hp : (1 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
    have hDv : 0 ≤ D v := hD v
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp hDv
  have hell : ell D ≤ ell (p • D) := Submodule.finrank_mono (lSpace_mono hle)
  have hcard := card_boundedArtinSchreierClasses_mul_card_lSpace p D hD
  rw [Module.natCard_eq_pow_finrank (K := k) (V := LSpace D),
    Module.natCard_eq_pow_finrank (K := k) (V := LSpace (p • D))] at hcard
  apply Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.card_pos (α := k)) (ell D))
  calc
    Nat.card (boundedArtinSchreierClasses p (p • D)) * Nat.card k ^ ell D =
        Nat.card k ^ ell (p • D) * p := hcard
    _ = (p * Nat.card k ^ (ell (p • D) - ell D)) * Nat.card k ^ ell D := by
      rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hell, mul_comm]

end FunctionField

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Nyll.GaloisCohomology.ArtinSchreier.CharacterClasses
import Nyll.GaloisCohomology.ArtinSchreier.FiniteRestrictionKernel

/-!
# Relative Artin--Schreier classes and Galois characters

The additive classes over the base field which acquire a root in a Galois
extension form the character group of that extension with values in the
prime field. The equivalence is constructed from actual roots, rather than
assuming a perfect pairing. Additive Hilbert 90 supplies every character;
Galois fixed-field descent proves injectivity.

For a finite extension this identifies the finite restriction kernel with
its cyclic character group. The construction also works for an infinite
Galois extension when the characters are continuous.
-/

noncomputable section

namespace ArtinSchreierTheory

universe u v

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} {L : Type v} [Field K] [Field L]
    [CharP K p] [CharP L p] [Algebra K L] [IsGalois K L]

/-- The Artin--Schreier classes split by the actual Galois extension are
exactly its continuous prime cyclic characters, compatibly with addition. -/
def restrictionKernelEquivCharacters :
    Multiplicative (classMap p (algebraMap K L)).ker ≃*
      (Gal(L/K) →ₜ* Multiplicative (ZMod p)) :=
  Classical.choice (by
    classical
    let R := (classMap p (algebraMap K L)).ker
    let Q := K ⧸ ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range
    have hroot (q : Multiplicative R) : ∃ (a : K) (β : L),
        (a : Q) = q.toAdd.val ∧ β ^ p - β = algebraMap K L a := by
      obtain ⟨a, ha⟩ := QuotientAddGroup.mk'_surjective
        ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range q.toAdd.val
      change (a : Q) = q.toAdd.val at ha
      have hz : (algebraMap K L a : L ⧸
          ((frobenius L p).toAddMonoidHom - AddMonoidHom.id L).range) = 0 := by
        change classMap p (algebraMap K L) a = 0
        rw [ha]
        exact q.toAdd.property
      obtain ⟨β, hβ⟩ := (QuotientAddGroup.eq_zero_iff (algebraMap K L a)).mp hz
      exact ⟨a, β, ha, hβ⟩
    choose a β ha hβ using hroot
    let e : Multiplicative R →* (Gal(L/K) →ₜ* Multiplicative (ZMod p)) :=
      MonoidHom.mk' (fun q => rootCharacter p L (a q) (β q) (hβ q)) (by
        intro q r
        have hsum : (β q + β r) ^ p - (β q + β r) =
            algebraMap K L (a q + a r) := by
          rw [add_pow_char, map_add]
          linear_combination hβ q + hβ r
        have hclass : (a (q * r) : Q) = (a q + a r : K) := by
          change (a (q * r) : Q) = QuotientAddGroup.mk'
            ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range (a q + a r)
          rw [map_add]
          change (a (q * r) : Q) = (a q : Q) + (a r : Q)
          exact (ha (q * r)).trans (congrArg₂ (· + ·) (ha q).symm (ha r).symm)
        rw [rootCharacter_eq_of_class_eq p (a (q * r)) (a q + a r)
          (β (q * r)) (β q + β r) (hβ (q * r)) hsum hclass]
        apply ContinuousMonoidHom.ext
        intro σ
        change (rootCharacter p L (a q + a r) (β q + β r) hsum σ).toAdd =
          (rootCharacter p L (a q) (β q) (hβ q) σ).toAdd +
            (rootCharacter p L (a r) (β r) (hβ r) σ).toAdd
        apply (ZMod.castHom (dvd_refl p) L).injective
        rw [map_add, rootCharacter_cast, rootCharacter_cast, rootCharacter_cast, map_add]
        ring)
    refine ⟨MulEquiv.ofBijective e ⟨?_, ?_⟩⟩
    · intro q r heq
      have hfixed (σ : Gal(L/K)) : σ (β q - β r) = β q - β r := by
        have h := congrArg
          (fun z : Multiplicative (ZMod p) => (ZMod.castHom (dvd_refl p) L) z.toAdd)
          (DFunLike.congr_fun heq σ)
        change (ZMod.castHom (dvd_refl p) L)
            ((rootCharacter p L (a q) (β q) (hβ q) σ).toAdd) =
          (ZMod.castHom (dvd_refl p) L)
            ((rootCharacter p L (a r) (β r) (hβ r) σ).toAdd) at h
        rw [rootCharacter_cast, rootCharacter_cast] at h
        rw [map_sub]
        linear_combination h
      obtain ⟨x, hx⟩ :=
        (InfiniteGalois.mem_range_algebraMap_iff_fixed (β q - β r)).mpr hfixed
      have hxAS : x ^ p - x = a q - a r := by
        apply (algebraMap K L).injective
        rw [map_sub, map_pow, hx, sub_pow_char, map_sub]
        linear_combination hβ q - hβ r
      change q.toAdd = r.toAdd
      apply Subtype.ext
      rw [← ha q, ← ha r]
      apply QuotientAddGroup.eq.mpr
      refine ⟨-x, ?_⟩
      change (-x) ^ p - (-x) = -(a q) + a r
      have hneg := map_neg
        ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K) x
      change (-x) ^ p - (-x) = -(x ^ p - x) at hneg
      rw [hneg, hxAS]
      ring
    · intro χ
      obtain ⟨a₀, β₀, hβ₀, hχ⟩ := exists_rootCharacter_eq p χ
      let q : R := ⟨(a₀ : Q), by
        change (algebraMap K L a₀ : L ⧸
          ((frobenius L p).toAddMonoidHom - AddMonoidHom.id L).range) = 0
        exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨β₀, hβ₀⟩⟩
      refine ⟨Multiplicative.ofAdd q, ?_⟩
      change rootCharacter p L (a (Multiplicative.ofAdd q))
        (β (Multiplicative.ofAdd q)) (hβ (Multiplicative.ofAdd q)) = χ
      exact (rootCharacter_eq_of_class_eq p (a (Multiplicative.ofAdd q)) a₀
        (β (Multiplicative.ofAdd q)) β₀ (hβ (Multiplicative.ofAdd q)) hβ₀
        (ha (Multiplicative.ofAdd q))).trans hχ)

end ArtinSchreierTheory

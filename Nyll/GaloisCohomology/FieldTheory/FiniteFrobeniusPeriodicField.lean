/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.FieldTheory.PeriodicSubfield
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The exact order on a Frobenius-periodic function field

The period-n subfield contains an actual copy of the degree-n extension of
the finite constant field. Restriction of its Frobenius therefore has order
exactly n, not just order dividing n.
-/

noncomputable section

namespace FiniteField

variable {k Ω F : Type*} [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω] [Field F] [Algebra Ω F]

/-- The period-n restriction of an automorphism extending arithmetic Frobenius has order n. -/
theorem orderOf_periodicAut_of_frobenius (σ : RingAut F)
    (hσ : ∀ a : Ω, σ (algebraMap Ω F a) =
      algebraMap Ω F (frobeniusAlgEquivOfAlgebraic k Ω a)) (n : ℕ) (hn : n ≠ 0) :
    orderOf (RingAut.periodicAut σ n) = n := by
  let : NeZero n := ⟨hn⟩
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k (ringChar k)⟩
  let E := Extension k (ringChar k) n
  let j : E →ₐ[k] Ω := IsAlgClosed.lift
  let τ := frobeniusAlgEquivOfAlgebraic k E
  have hτ : orderOf τ = n :=
    (orderOf_frobeniusAlgEquivOfAlgebraic k E).trans (finrank_extension k (ringChar k) n)
  have hτn : τ ^ n = 1 :=
    (congrArg (fun i : ℕ => τ ^ i) hτ).symm.trans (pow_orderOf_eq_one τ)
  have hj (a : E) : σ (algebraMap Ω F (j a)) = algebraMap Ω F (j (τ a)) := by
    rw [hσ]
    change algebraMap Ω F ((j a) ^ Fintype.card k) =
      algebraMap Ω F (j (a ^ Fintype.card k))
    exact congrArg (algebraMap Ω F) (j.map_pow a (Fintype.card k)).symm
  have hjpow (i : ℕ) (a : E) :
      (σ ^ i) (algebraMap Ω F (j a)) = algebraMap Ω F (j ((τ ^ i) a)) := by
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ', RingAut.mul_apply, ih, hj, pow_succ', AlgEquiv.mul_apply]
  have hjmem (a : E) : (σ ^ n) (algebraMap Ω F (j a)) = algebraMap Ω F (j a) :=
    (hjpow n a).trans (congrArg (fun y : E => algebraMap Ω F (j y))
      (AlgEquiv.congr_fun hτn a))
  let jF : E →+* RingAut.periodicSubfield σ n :=
    { toFun a := ⟨algebraMap Ω F (j a), hjmem a⟩
      map_zero' := Subtype.ext (((algebraMap Ω F).comp j.toRingHom).map_zero)
      map_one' := Subtype.ext (((algebraMap Ω F).comp j.toRingHom).map_one)
      map_add' a b := Subtype.ext (((algebraMap Ω F).comp j.toRingHom).map_add a b)
      map_mul' a b := Subtype.ext (((algebraMap Ω F).comp j.toRingHom).map_mul a b) }
  have horder : τ ^ orderOf (RingAut.periodicAut σ n) = 1 := by
    ext a
    apply jF.injective
    apply Subtype.ext
    change algebraMap Ω F (j ((τ ^ orderOf (RingAut.periodicAut σ n)) a)) =
      algebraMap Ω F (j a)
    rw [← hjpow]
    have h := RingAut.periodicAut_pow_coe σ n (orderOf (RingAut.periodicAut σ n)) (jF a)
    rw [pow_orderOf_eq_one] at h
    exact h.symm
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one (RingAut.periodicAut_pow_period σ n)
  · have hdiv : orderOf τ ∣ orderOf (RingAut.periodicAut σ n) :=
      orderOf_dvd_of_pow_eq_one horder
    exact (dvd_of_eq hτ.symm).trans hdiv

end FiniteField

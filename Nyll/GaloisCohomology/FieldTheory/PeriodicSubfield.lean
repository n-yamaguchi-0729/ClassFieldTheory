/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Ring.Action.End

/-!
# Restricting an automorphism to its periodic subfield

Elements fixed by the n-th power form an actual subfield. The original
automorphism restricts to it, and its n-th power is the identity there.
-/

namespace RingAut

variable {F : Type*} [Field F]

/-- The actual subfield fixed by the n-th power of an automorphism. -/
def periodicSubfield (σ : RingAut F) (n : ℕ) : Subfield F :=
  (σ ^ n).toRingHom.eqLocusField (RingHom.id F)

/-- Membership in a periodic subfield is precisely the specified periodicity equation. -/
theorem mem_periodicSubfield (σ : RingAut F) (n : ℕ) (x : F) :
    x ∈ periodicSubfield σ n ↔ (σ ^ n) x = x := Iff.rfl

/-- The original automorphism restricts to the actual periodic subfield. -/
def periodicAut (σ : RingAut F) (n : ℕ) : RingAut (periodicSubfield σ n) where
  toFun x := ⟨σ (x : F), by
    have hx : (σ ^ n) (x : F) = x := x.property
    change (σ ^ n) (σ (x : F)) = σ (x : F)
    rw [← RingAut.mul_apply, ← pow_succ, pow_succ', RingAut.mul_apply, hx]⟩
  invFun x := ⟨σ.symm (x : F), by
    have hx : (σ ^ n) (x : F) = x := x.property
    change (σ ^ n) (σ.symm (x : F)) = σ.symm (x : F)
    apply σ.injective
    rw [← RingAut.mul_apply, ← pow_succ', pow_succ, RingAut.mul_apply,
      RingEquiv.apply_symm_apply, hx]⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x)
  right_inv x := Subtype.ext (σ.apply_symm_apply x)
  map_add' x y := Subtype.ext (σ.map_add x y)
  map_mul' x y := Subtype.ext (σ.map_mul x y)

/-- Restriction preserves every nonnegative power on the underlying field elements. -/
theorem periodicAut_pow_coe (σ : RingAut F) (n i : ℕ) (x : periodicSubfield σ n) :
    (((periodicAut σ n) ^ i) x : F) = (σ ^ i) (x : F) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ', RingAut.mul_apply]
    change σ ((((periodicAut σ n) ^ i) x) : F) = (σ ^ (i + 1)) (x : F)
    rw [ih, pow_succ', RingAut.mul_apply]

/-- The restricted automorphism has exponent dividing the prescribed period. -/
theorem periodicAut_pow_period (σ : RingAut F) (n : ℕ) : (periodicAut σ n) ^ n = 1 := by
  ext x
  exact (periodicAut_pow_coe σ n n x).trans x.property

end RingAut

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Degree of a compositum of finite fields

When two intermediate fields generate a finite ambient field, its degree is
the least common multiple of their degrees. The proof restricts the ambient
Frobenius to each generating subfield and compares their orders.
-/

namespace FiniteField

variable {k E : Type*} [Field k] [Field E] [Algebra k E] [Finite E]

/-- Two subfields generating a finite field have compositum degree equal to
the least common multiple of their degrees. -/
theorem finrank_eq_lcm_of_sup_eq_top (A B : IntermediateField k E)
    (h : A ⊔ B = ⊤) :
    Module.finrank k E = Nat.lcm (Module.finrank k A) (Module.finrank k B) := by
  have : Finite k := Finite.of_injective (algebraMap k E) (algebraMap k E).injective
  let : Fintype k := Fintype.ofFinite k
  let σ : E ≃ₐ[k] E := frobeniusAlgEquivOfAlgebraic k E
  have hrestrict (D : IntermediateField k E) :
      AlgEquiv.restrictNormalHom D σ = frobeniusAlgEquivOfAlgebraic k D := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    calc
      ((AlgEquiv.restrictNormalHom D σ x : D) : E) = σ (x : E) :=
        AlgEquiv.restrictNormalHom_apply D σ x
      _ = (x : E) ^ Fintype.card k := rfl
      _ = ((frobeniusAlgEquivOfAlgebraic k D x : D) : E) :=
        (map_pow D.val x (Fintype.card k)).symm
  have hfix (D : IntermediateField k E) (n : ℕ) (hn : Module.finrank k D ∣ n) :
      σ ^ n ∈ D.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker D, MonoidHom.mem_ker, map_pow,
      hrestrict D]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [orderOf_frobeniusAlgEquivOfAlgebraic]
    exact hn
  have hpow : σ ^ Nat.lcm (Module.finrank k A) (Module.finrank k B) = 1 := by
    have hmem : σ ^ Nat.lcm (Module.finrank k A) (Module.finrank k B) ∈
        (A ⊔ B).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hfix A _ (Nat.dvd_lcm_left _ _), hfix B _ (Nat.dvd_lcm_right _ _)⟩
    rw [h, IntermediateField.fixingSubgroup_top, Subgroup.mem_bot] at hmem
    exact hmem
  apply Nat.dvd_antisymm
  · rw [← orderOf_frobeniusAlgEquivOfAlgebraic k E]
    exact orderOf_dvd_iff_pow_eq_one.mpr hpow
  · exact Nat.lcm_dvd (Module.finrank_dvd_finrank_right k A E)
      (Module.finrank_dvd_finrank_right k B E)

end FiniteField

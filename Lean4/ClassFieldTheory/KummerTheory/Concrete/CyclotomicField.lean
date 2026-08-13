import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# Concrete cyclotomic fields

This file records two structural facts about the concrete cyclotomic-field
model: it admits a primitive generator of the defining order, and divisibility
of orders induces an algebra homomorphism between the corresponding fields.
-/

noncomputable section

namespace KummerTheory

/-- A concrete cyclotomic field has a primitive generator of its defining
order. -/
theorem exists_primitiveRoot_adjoin_eq_top_cyclotomicField
    (K : Type) [Field K] [CharZero K] (m : ℕ) (hm : 0 < m) :
    ∃ ζ : CyclotomicField m K,
      IsPrimitiveRoot ζ m ∧ Algebra.adjoin K ({ζ} : Set _) = ⊤ := by
  letI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨ζ, hζ⟩ :=
    (CyclotomicField.isCyclotomicExtension m K).exists_isPrimitiveRoot
      (Set.mem_singleton m) hm.ne'
  exact ⟨ζ, hζ,
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ⟩

/-- If `a` divides `b`, the concrete cyclotomic field of order `a` embeds in
the concrete cyclotomic field of order `b`. -/
theorem nonempty_algHom_cyclotomicField_of_dvd
    (K : Type) [Field K] [CharZero K]
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ∣ b) :
    Nonempty (CyclotomicField a K →ₐ[K] CyclotomicField b K) := by
  letI : NeZero a := ⟨ha.ne'⟩
  letI : NeZero b := ⟨hb.ne'⟩
  let A := CyclotomicField a K
  let B := CyclotomicField b K
  letI : IsCyclotomicExtension {a} K A :=
    CyclotomicField.isCyclotomicExtension a K
  letI : IsCyclotomicExtension {b} K B :=
    CyclotomicField.isCyclotomicExtension b K
  letI : FiniteDimensional K B :=
    IsCyclotomicExtension.finiteDimensional {b} K B
  obtain ⟨ζ, hζ⟩ :=
    (CyclotomicField.isCyclotomicExtension b K).exists_isPrimitiveRoot
      (Set.mem_singleton b) hb.ne'
  obtain ⟨c, hbc⟩ := hab
  have hc : c ≠ 0 := by
    intro hc0
    subst c
    simp at hbc
    omega
  have hζa : IsPrimitiveRoot (ζ ^ c) a := by
    have hpow := hζ.pow_of_dvd hc (by
      rw [hbc]
      exact dvd_mul_left c a)
    have hdiv : b / c = a := by
      rw [hbc, Nat.mul_div_left a (Nat.pos_of_ne_zero hc)]
    simpa only [hdiv] using hpow
  let E : IntermediateField K B := IntermediateField.adjoin K {ζ ^ c}
  letI : IsCyclotomicExtension {a} K E :=
    hζa.intermediateField_adjoin_isCyclotomicExtension K
  let e : A ≃ₐ[K] E := IsCyclotomicExtension.algEquiv {a} K A E
  exact ⟨E.val.comp e.toAlgHom⟩

end KummerTheory

end

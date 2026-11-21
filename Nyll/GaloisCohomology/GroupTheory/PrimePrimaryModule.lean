/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.Int.Basic

/-! # Exact prime-primary reduction with a preserved scalar action -/

@[expose] public section

open Function Module

namespace Submodule

variable {p : ℕ} {R : Type*} [Ring R]
  {A B C : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

private theorem pow_nsmul_eq_zero_of_le {M : Type*} [AddCommGroup M] {x : M}
    {a b : ℕ} (hab : a ≤ b) (ha : p ^ a • x = 0) : p ^ b • x = 0 := by
  have hb : b = (b - a) + a := (Nat.sub_add_cancel hab).symm
  rw [hb, pow_add, ← smul_smul, ha, nsmul_zero]

/-- The prime-power torsion subgroup, with its original scalar action. -/
def primePrimary (p : ℕ) (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] : Submodule R M where
  carrier := {x | ∃ a : ℕ, p ^ a • x = 0}
  zero_mem' := ⟨0, nsmul_zero _⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨max a b, ?_⟩
    rw [nsmul_add, pow_nsmul_eq_zero_of_le (le_max_left a b) ha,
      pow_nsmul_eq_zero_of_le (le_max_right a b) hb, add_zero]
  smul_mem' := by
    rintro r x ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have h := map_nsmul (DistribSMul.toAddMonoidHom M r) (p ^ a) x
    change r • (p ^ a • x) = p ^ a • (r • x) at h
    rw [← h, ha, smul_zero]

theorem mem_primePrimary {x : A} : x ∈ primePrimary p R A ↔ ∃ a : ℕ, p ^ a • x = 0 := Iff.rfl

/-- A homomorphism restricts to the actual primary components. -/
def primePrimaryMap (p : ℕ) (f : A →ₗ[R] B) : primePrimary p R A →ₗ[R] primePrimary p R B :=
  f.restrict (by
    rintro x ⟨a, ha⟩
    exact ⟨a, by rw [← map_nsmul, ha, map_zero]⟩)

theorem primePrimaryMap_apply (f : A →ₗ[R] B) (x : primePrimary p R A) :
    (primePrimaryMap p f x : B) = f x := rfl

theorem primePrimaryMap_injective (f : A →ₗ[R] B) (hf : Injective f) :
    Injective (primePrimaryMap p f) := fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h))

theorem primePrimaryMap_exact (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Injective f) (h : Exact f g) : Exact (primePrimaryMap p f) (primePrimaryMap p g) := by
  intro b
  constructor
  · intro hb
    obtain ⟨a, ha⟩ := (h b.val).mp (congrArg Subtype.val hb)
    obtain ⟨k, hk⟩ := mem_primePrimary.mp b.property
    have ha' : p ^ k • a = 0 := by
      apply hf
      rw [map_nsmul, ha, hk, map_zero]
    exact ⟨⟨a, ⟨k, ha'⟩⟩, Subtype.ext ha⟩
  · rintro ⟨a, rfl⟩
    exact Subtype.ext (h.apply_apply_eq_zero a.val)

private theorem mem_primePrimary_iff_int_ideal {x : A} :
    x ∈ primePrimary p R A ↔ x ∈ Ideal.primaryComponent A (Ideal.span {(p : ℤ)}) := by
  rw [mem_primePrimary, Ideal.primaryComponent_mem]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, (mem_torsionBySet_iff _ _).mpr ?_⟩
    rintro ⟨a, ha⟩
    have hmem : a ∈ Ideal.span ({(p : ℤ) ^ k} : Set ℤ) := by
      rw [← Ideal.span_singleton_pow]
      exact ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hmem
    change a • x = 0
    rw [hb, mul_comm, mul_smul, ← Nat.cast_pow, natCast_zsmul, hk, smul_zero]
  · rintro ⟨k, hk⟩
    have hmem : (p : ℤ) ^ k ∈ (Ideal.span {(p : ℤ)}) ^ k :=
      Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _
    refine ⟨k, ?_⟩
    have hzero := (mem_torsionBySet_iff _ _).mp hk ⟨_, hmem⟩
    change (p : ℤ) ^ k • x = 0 at hzero
    simpa only [← Nat.cast_pow, natCast_zsmul] using hzero

/-- Primary reduction preserves a surjection between finite modules. The
surjective lift comes from the integral primary decomposition. -/
theorem primePrimaryMap_surjective (hp : p.Prime) [Finite A] (f : A →ₗ[R] B)
    (hf : Surjective f) : Surjective (primePrimaryMap p f) := by
  let P : IsDedekindDomain.HeightOneSpectrum ℤ :=
    { asIdeal := Ideal.span {(p : ℤ)}
      isPrime := (Ideal.span_singleton_prime (Int.natCast_ne_zero.mpr hp.ne_zero)).mpr
        (Int.prime_iff_natAbs_prime.mpr hp)
      ne_bot := fun h => hp.ne_zero (Int.natCast_eq_zero.mp (Ideal.span_singleton_eq_bot.mp h)) }
  let f₀ := f.toAddMonoidHom.toIntLinearMap
  have hTor : IsTorsion ℤ A := isAddTorsion_iff_isTorsion_int.mp isAddTorsion_of_finite
  intro b
  obtain ⟨a, ha⟩ := Ideal.primaryComponent.map_surjective hTor P f₀ hf
    ⟨b.val, mem_primePrimary_iff_int_ideal.mp b.property⟩
  refine ⟨⟨a.val, mem_primePrimary_iff_int_ideal.mpr a.property⟩, ?_⟩
  have h := congrArg (fun x : Ideal.primaryComponent B P.asIdeal => (x : B)) ha
  exact Subtype.ext h

/-- A finite primary component is killed by one positive power of the prime. -/
theorem exists_pow_nsmul_eq_zero_primePrimary [Finite A] (p : ℕ) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : primePrimary p R A, p ^ m • x = 0 := by
  classical
  let := Fintype.ofFinite (primePrimary p R A)
  have hex (x : primePrimary p R A) : ∃ a : ℕ, p ^ a • x = 0 := by
    obtain ⟨a, ha⟩ := mem_primePrimary.mp x.property
    exact ⟨a, Subtype.ext ha⟩
  choose a ha using hex
  let m := (Finset.univ.sup a) + 1
  refine ⟨m, Nat.succ_pos _, fun x => ?_⟩
  exact pow_nsmul_eq_zero_of_le
    ((Finset.le_sup (f := a) (Finset.mem_univ x)).trans (Nat.le_succ _)) (ha x)

end Submodule

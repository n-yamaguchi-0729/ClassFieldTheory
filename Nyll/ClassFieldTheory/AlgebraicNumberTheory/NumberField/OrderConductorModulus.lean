/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.FractionalIdealFactorization
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.OrderConductor
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.FullModulus
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.ClassGroup.Basic

/-! # The full ray modulus of an integer order's conductor -/

@[expose] public section

open scoped NumberField nonZeroDivisors
open ClassFieldTheory
open IsDedekindDomain UniqueFactorizationMonoid
open ClassFieldTheory.FractionalIdealFactorization

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]
    (O : Subalgebra ℤ K) [Module.Finite ℤ O] [IsFractionRing O K]

/-- The conductor modulus retains every finite prime exponent and imposes no real positivity. -/
noncomputable def orderConductorModulus : RayClass.Modulus K :=
  RayClass.Modulus.ofFinite (Finsupp.mapRange Int.toNat rfl
    (NumberFieldFractionalIdealGroup.countVector (FractionalIdeal.mk0 K
      ⟨orderConductor O, mem_nonZeroDivisors_iff_ne_zero.mpr (orderConductor_ne_bot O)⟩)))

/-- The exponent at each finite place is the multiplicity of the actual conductor ideal. -/
theorem orderConductorModulus_finitePart (v : HeightOneSpectrum (𝓞 K)) :
    (orderConductorModulus O).finitePart v = multiplicity v.asIdeal (orderConductor O) := by
  change (FractionalIdeal.count K v
    (orderConductor O : FractionalIdeal (𝓞 K)⁰ K)).toNat = _
  rw [count_coeIdeal_eq_multiplicity (F := K) v (orderConductor_ne_bot O), Int.toNat_natCast]

@[simp]
theorem orderConductorModulus_infinitePart : (orderConductorModulus O).infinitePart = ∅ := rfl

/-- The finite support consists precisely of the primes containing the conductor. -/
theorem mem_orderConductorModulus_support_iff (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ (orderConductorModulus O).finitePart.support ↔ orderConductor O ≤ v.asIdeal := by
  rw [Finsupp.mem_support_iff, orderConductorModulus_finitePart,
    multiplicity_ne_zero_iff_le v (orderConductor_ne_bot O)]

/-- Inclusion of integer orders reverses divisibility of their conductor moduli. -/
theorem orderConductorModulus_antitone
    {P : Subalgebra ℤ K} [Module.Finite ℤ P] [IsFractionRing P K] (h : O ≤ P) :
    orderConductorModulus P ≤ orderConductorModulus O := by
  constructor
  · intro v
    rw [orderConductorModulus_finitePart, orderConductorModulus_finitePart]
    exact v.multiplicity_le_of_ideal_ge (orderConductor_mono h) (orderConductor_ne_bot O)
  · exact fun _ hx => hx

theorem orderConductorModulus_eq_zero_of_conductor_eq_top (h : orderConductor O = ⊤) :
    orderConductorModulus O = 0 := by
  apply RayClass.Modulus.ext
  · apply Finsupp.ext
    intro v
    change (orderConductorModulus O).finitePart v = 0
    apply Finsupp.notMem_support_iff.mp
    intro hv
    have hv' := (mem_orderConductorModulus_support_iff O v).mp hv
    rw [h, top_le_iff] at hv'
    exact v.isMaximal.ne_top hv'
  · rfl

/-- An integral element belongs to the conductor exactly when it belongs to all its prime powers. -/
theorem mem_orderConductor_iff_forall_mem_prime_pow (x : 𝓞 K) :
    x ∈ orderConductor O ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      x ∈ v.asIdeal ^ (orderConductorModulus O).finitePart v := by
  rw [← Ideal.iInf_maxPowDividing_eq (orderConductor_ne_bot O), Submodule.mem_iInf]
  simp only [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity (orderConductor_ne_bot O),
    orderConductorModulus_finitePart]

/-- For a nonzero integral ideal the ray support criterion is coprimality to the conductor. -/
theorem orderIdeal_coprime_conductor_iff (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    I ⊔ orderConductor O = ⊤ ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      v ∈ (orderConductorModulus O).finitePart.support →
        FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  have hcount (v : HeightOneSpectrum (𝓞 K)) :
      FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 ↔ I ≤ v.asIdeal := by
    rw [count_coeIdeal_eq_multiplicity (F := K) v hI, Nat.cast_ne_zero,
      multiplicity_ne_zero_iff_le v hI]
  constructor
  · intro h v hv
    by_contra hn
    have hle := sup_le ((hcount v).mp hn) ((mem_orderConductorModulus_support_iff O v).mp hv)
    rw [h, top_le_iff] at hle
    exact v.isMaximal.ne_top hle
  · intro h
    by_contra hn
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hn
    have hcond : orderConductor O ≤ P := le_sup_right.trans hle
    have hP0 : P ≠ ⊥ := by
      intro hbot
      exact orderConductor_ne_bot O (le_bot_iff.mp (hbot ▸ hcond))
    let v : HeightOneSpectrum (𝓞 K) := ⟨P, hP.isPrime, hP0⟩
    exact (hcount v).mpr (le_sup_left.trans hle)
      (h v ((mem_orderConductorModulus_support_iff O v).mpr hcond))

end NumberField

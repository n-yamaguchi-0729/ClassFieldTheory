/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.Integer

/-!
# Conductors of arbitrary full integer orders

An order is an actual integer subalgebra of a number field, finite over the
integers and with the original number field as its fraction field. Its
conductor is the largest ideal of the ring of integers contained in that
subalgebra. Clearing the denominators of a finite integer generating set of
the maximal order proves that the conductor is nonzero. No Dedekind property
of the smaller order is assumed.
-/

@[expose] public section

open scoped NumberField nonZeroDivisors

namespace NumberField

variable {K : Type*} [Field K]

/-- Every integer-finite subalgebra lies in the actual integral closure. -/
theorem finiteSubalgebra_le_ringOfIntegers
    (O : Subalgebra ℤ K) [Module.Finite ℤ O] : O ≤ integralClosure ℤ K := by
  intro x hx
  exact (O.isIntegral_iff.mp (inferInstance : Algebra.IsIntegral ℤ O)) x hx

/-- The original inclusion of an order into the ring of integers. -/
def orderToRingOfIntegers
    (O : Subalgebra ℤ K) [Module.Finite ℤ O] : O →ₐ[ℤ] 𝓞 K :=
  Subalgebra.inclusion (finiteSubalgebra_le_ringOfIntegers O)

/-- The order inclusion preserves the actual element of the number field. -/
@[simp]
theorem orderToRingOfIntegers_coe
    (O : Subalgebra ℤ K) [Module.Finite ℤ O] (x : O) :
    (orderToRingOfIntegers O x : K) = (x : K) := rfl

/-- The conductor consists of the integral elements whose products with
all integral elements belong to the original order. -/
def orderConductor (O : Subalgebra ℤ K) : Ideal (𝓞 K) where
  carrier := {x | ∀ y : 𝓞 K, (x : K) * (y : K) ∈ O}
  zero_mem' y := by
    change (0 : K) * (y : K) ∈ O
    rw [zero_mul]
    exact O.zero_mem
  add_mem' {x z} hx hz y := by
    change ((x : K) + (z : K)) * (y : K) ∈ O
    rw [add_mul]
    exact O.add_mem (hx y) (hz y)
  smul_mem' a x hx y := by
    change (a : K) * (x : K) * (y : K) ∈ O
    rw [mul_assoc, mul_left_comm]
    exact hx (a * y)

/-- Membership uses multiplication in the original number field. -/
theorem mem_orderConductor_iff
    (O : Subalgebra ℤ K) (x : 𝓞 K) :
    x ∈ orderConductor O ↔ ∀ y : 𝓞 K, (x : K) * (y : K) ∈ O := Iff.rfl

/-- Every conductor element itself belongs to the order. -/
theorem orderConductor_mem_order
    (O : Subalgebra ℤ K) {x : 𝓞 K} (hx : x ∈ orderConductor O) : (x : K) ∈ O := by
  have h := hx 1
  change (x : K) * 1 ∈ O at h
  rwa [mul_one] at h

/-- The conductor is the largest integral ideal contained in the order. -/
theorem le_orderConductor_iff
    (O : Subalgebra ℤ K) (I : Ideal (𝓞 K)) :
    I ≤ orderConductor O ↔ ∀ x ∈ I, (x : K) ∈ O := by
  constructor
  · intro h x hx
    exact orderConductor_mem_order O (h hx)
  · intro h x hx y
    exact h (x * y) (I.mul_mem_right y hx)

/-- Enlarging an order enlarges its conductor ideal. -/
theorem orderConductor_mono
    {O P : Subalgebra ℤ K} (h : O ≤ P) : orderConductor O ≤ orderConductor P :=
  fun _ hx y => h (hx y)

/-- The conductor is the unit ideal exactly when all integral elements
already belong to the given subalgebra. -/
theorem orderConductor_eq_top_iff
    (O : Subalgebra ℤ K) :
    orderConductor O = ⊤ ↔ integralClosure ℤ K ≤ O := by
  constructor
  · intro h x hx
    let y : 𝓞 K := ⟨x, hx⟩
    have htop : y ∈ (⊤ : Ideal (𝓞 K)) := Submodule.mem_top
    exact orderConductor_mem_order O (h.symm ▸ htop)
  · intro h
    apply top_unique
    intro x _ y
    exact h ((x * y : 𝓞 K).property)

/-- Among finite integer orders, conductor one characterizes the maximal order. -/
theorem orderConductor_eq_top_iff_eq_ringOfIntegers
    (O : Subalgebra ℤ K) [Module.Finite ℤ O] :
    orderConductor O = ⊤ ↔ O = integralClosure ℤ K := by
  rw [orderConductor_eq_top_iff]
  exact ⟨fun h => le_antisymm (finiteSubalgebra_le_ringOfIntegers O) h,
    fun h => h.symm.le⟩

/-- A full finite integer order has nonzero conductor. A common denominator
for finitely many generators of the maximal order supplies an actual nonzero
element of the conductor, without assuming that the order is Dedekind. -/
theorem orderConductor_ne_bot [NumberField K]
    (O : Subalgebra ℤ K) [Module.Finite ℤ O] [IsFractionRing O K] :
    orderConductor O ≠ ⊥ := by
  obtain ⟨s, hs⟩ := Module.finite_def.mp (inferInstance : Module.Finite ℤ (𝓞 K))
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples O⁰ s
    (fun x : 𝓞 K => (x : K))
  let D : Submodule ℤ (𝓞 K) := O.toSubmodule.comap
    ((Algebra.lmul ℤ K ((d : O) : K)).comp
      (IsScalarTower.toAlgHom ℤ (𝓞 K) K).toLinearMap)
  have hsD : Submodule.span ℤ (s : Set (𝓞 K)) ≤ D := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨a, ha⟩ := hd x hx
    change algebraMap O K a = (d : O) • (x : K) at ha
    rw [Algebra.smul_def] at ha
    change ((d : O) : K) * (x : K) ∈ O
    exact ha ▸ a.property
  let c : 𝓞 K := orderToRingOfIntegers O (d : O)
  have hc : c ∈ orderConductor O := by
    intro y
    exact hsD (hs.symm ▸ (Submodule.mem_top : y ∈ (⊤ : Submodule ℤ (𝓞 K))))
  have hc0 : c ≠ 0 := by
    intro h
    apply nonZeroDivisors.ne_zero d.property
    apply Subtype.ext
    exact congrArg (fun x : 𝓞 K => (x : K)) h
  intro hbot
  have hc' : c ∈ (⊥ : Ideal (𝓞 K)) := hbot ▸ hc
  exact hc0 ((Submodule.mem_bot (R := 𝓞 K)).mp hc')

end NumberField

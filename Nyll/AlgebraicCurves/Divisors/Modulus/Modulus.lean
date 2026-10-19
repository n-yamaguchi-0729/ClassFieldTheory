/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Mathlib.Data.Finsupp.Order
import Mathlib.RingTheory.Ideal.Operations

/-!
# Function-field moduli and local congruence

A modulus retains the natural-number multiplicity at each place. Congruence to
one is expressed in powers of the maximal ideal of the actual valuation ring,
and includes a local unit. In particular, it never uses the convention `ord 0 = 0`
to assert that zero is a unit. The global condition explicitly excludes zero,
including when the modulus is zero.

The mathematical convention is Serre, *Algebraic Groups and Class Fields*,
Chapter V, §1, no. 1–2. The places and valuation orders are supplied by
`Divisors.ClassGroup`; no uniformizer is chosen in the definition.
-/

noncomputable section

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- A function-field modulus: finitely supported nonnegative multiplicities. -/
abbrev Modulus := Place K F →₀ ℕ

namespace Place

variable {K F}

/-- Congruence to one modulo the `n`-th power of the maximal ideal, with an
actual valuation-ring unit representing the rational function. -/
def CongruentOne (v : Place K F) (n : ℕ) (f : F) : Prop :=
  ∃ u : v.toValuationSubringˣ,
    ((u : v.toValuationSubring) : F) = f ∧
      (u : v.toValuationSubring) - 1 ∈
        (IsLocalRing.maximalIdeal v.toValuationSubring) ^ n

namespace CongruentOne

variable {v : Place K F} {n m : ℕ} {f g : F}

/-- A local congruence witness is necessarily a nonzero rational function. -/
theorem ne_zero (hf : v.CongruentOne n f) : f ≠ 0 := by
  obtain ⟨u, rfl, _⟩ := hf
  simpa only [ne_eq, ZeroMemClass.coe_eq_zero] using u.ne_zero

/-- The identity is congruent to one at every multiplicity. -/
theorem one (v : Place K F) (n : ℕ) : v.CongruentOne n 1 := by
  refine ⟨1, rfl, ?_⟩
  change (1 : v.toValuationSubring) - 1 ∈
    (IsLocalRing.maximalIdeal v.toValuationSubring) ^ n
  rw [sub_self]
  exact Ideal.zero_mem _

/-- Local congruence to one is closed under products. -/
theorem mul (hf : v.CongruentOne n f) (hg : v.CongruentOne n g) :
    v.CongruentOne n (f * g) := by
  obtain ⟨u, rfl, hu⟩ := hf
  obtain ⟨w, rfl, hw⟩ := hg
  refine ⟨u * w, rfl, ?_⟩
  have h := ((IsLocalRing.maximalIdeal v.toValuationSubring) ^ n).add_mem
    (((IsLocalRing.maximalIdeal v.toValuationSubring) ^ n).mul_mem_right
      (w : v.toValuationSubring) hu) hw
  convert h using 1
  simp only [Units.val_mul]
  ring

/-- Local congruence to one is closed under inverses. -/
theorem inv (hf : v.CongruentOne n f) : v.CongruentOne n f⁻¹ := by
  obtain ⟨u, rfl, hu⟩ := hf
  refine ⟨u⁻¹, ?_, ?_⟩
  · have h := congrArg (fun a : v.toValuationSubring => (a : F)) u.inv_val
    exact eq_inv_of_mul_eq_one_left h
  · have h := ((IsLocalRing.maximalIdeal v.toValuationSubring) ^ n).mul_mem_left
      (-((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring)) hu
    have heq : -((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) *
        ((u : v.toValuationSubring) - 1) =
        ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) - 1 := by
      rw [neg_mul, mul_sub, Units.inv_mul, mul_one]
      ring
    rwa [heq] at h

/-- A congruence at a larger multiplicity implies every weaker congruence. -/
theorem mono (hf : v.CongruentOne n f) (hmn : m ≤ n) : v.CongruentOne m f := by
  obtain ⟨u, hu, hmem⟩ := hf
  exact ⟨u, hu, Ideal.pow_le_pow_right hmn hmem⟩

/-- A rational function congruent to one has no zero or pole at this place. -/
theorem ord_eq_zero (hf : v.CongruentOne n f) : v.ord f = 0 := by
  obtain ⟨u, rfl, _⟩ := hf
  exact v.ord_coe_unit u

end CongruentOne

/-- Local congruence at exponent zero is exactly representation by a local unit. -/
theorem congruentOne_zero_iff (v : Place K F) (f : F) :
    v.CongruentOne 0 f ↔
      ∃ u : v.toValuationSubringˣ, ((u : v.toValuationSubring) : F) = f := by
  constructor
  · rintro ⟨u, hu, _⟩
    exact ⟨u, hu⟩
  · rintro ⟨u, hu⟩
    refine ⟨u, hu, ?_⟩
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

end Place

namespace Modulus

variable {K F}

/-- The effective integer divisor associated with a modulus. -/
def toDivisor (D : Modulus K F) : Divisor K F :=
  D.mapRange (fun n : ℕ => (n : ℤ)) (by rfl)

@[simp]
theorem toDivisor_apply (D : Modulus K F) (v : Place K F) :
    D.toDivisor v = (D v : ℤ) := rfl

@[simp]
theorem toDivisor_zero : (0 : Modulus K F).toDivisor = 0 := by
  ext v
  change ((0 : ℕ) : ℤ) = 0
  exact Nat.cast_zero

@[simp]
theorem toDivisor_add (D E : Modulus K F) :
    (D + E).toDivisor = D.toDivisor + E.toDivisor := by
  ext v
  change ((D v + E v : ℕ) : ℤ) = (D v : ℤ) + (E v : ℤ)
  exact Nat.cast_add (D v) (E v)

/-- The degree includes residue-field degrees over an arbitrary base field. -/
def degree (D : Modulus K F) : ℤ := Divisor.degree D.toDivisor

@[simp]
theorem degree_zero : (0 : Modulus K F).degree = 0 := by
  rw [degree, toDivisor_zero, map_zero]

@[simp]
theorem degree_add (D E : Modulus K F) : (D + E).degree = D.degree + E.degree := by
  change Divisor.degree (D + E).toDivisor =
    Divisor.degree D.toDivisor + Divisor.degree E.toDivisor
  rw [toDivisor_add, map_add]

/-- A globally nonzero rational function congruent to one at every place in
the support, with the full multiplicity at that place. -/
def CongruentOne (D : Modulus K F) (f : F) : Prop :=
  f ≠ 0 ∧ ∀ v : Place K F, D v ≠ 0 → v.CongruentOne (D v) f

namespace CongruentOne

variable {D E : Modulus K F} {f g : F}

theorem ne_zero (hf : D.CongruentOne f) : f ≠ 0 := hf.1

/-- Global modulus congruence is satisfied by one. -/
theorem one (D : Modulus K F) : D.CongruentOne 1 :=
  ⟨one_ne_zero, fun v _ => Place.CongruentOne.one v (D v)⟩

/-- Global modulus congruence is closed under products. -/
theorem mul (hf : D.CongruentOne f) (hg : D.CongruentOne g) :
    D.CongruentOne (f * g) :=
  ⟨mul_ne_zero hf.1 hg.1, fun v hv => (hf.2 v hv).mul (hg.2 v hv)⟩

/-- Global modulus congruence is closed under inverses. -/
theorem inv (hf : D.CongruentOne f) : D.CongruentOne f⁻¹ :=
  ⟨inv_ne_zero hf.1, fun v hv => (hf.2 v hv).inv⟩

/-- Global modulus congruence is closed under quotients. -/
theorem div (hf : D.CongruentOne f) (hg : D.CongruentOne g) :
    D.CongruentOne (f / g) := by
  simpa only [div_eq_mul_inv] using hf.mul hg.inv

/-- Restrict a modulus congruence to a smaller effective divisor. -/
theorem mono (hf : D.CongruentOne f) (hED : E ≤ D) : E.CongruentOne f := by
  refine ⟨hf.1, fun v hv => ?_⟩
  have hDv : D v ≠ 0 := by
    intro h
    exact hv (Nat.eq_zero_of_le_zero (h ▸ hED v))
  exact (hf.2 v hDv).mono (hED v)

/-- The principal divisor of a congruent function avoids the modulus support. -/
theorem ord_eq_zero (hf : D.CongruentOne f) (v : Place K F) (hv : D v ≠ 0) :
    v.ord f = 0 := (hf.2 v hv).ord_eq_zero

end CongruentOne

/-- At zero modulus the only condition is that the rational function be nonzero. -/
@[simp]
theorem congruentOne_zero (f : F) :
    (0 : Modulus K F).CongruentOne f ↔ f ≠ 0 := by
  constructor
  · exact And.left
  · intro hf
    exact ⟨hf, fun _ hv => False.elim (hv rfl)⟩

/-- Zero is never an admissible rational function, even for zero modulus. -/
@[simp]
theorem not_congruentOne_zero (D : Modulus K F) : ¬ D.CongruentOne (0 : F) :=
  fun h => h.ne_zero rfl

/-- Congruence at a one-point modulus keeps its specified multiplicity. -/
theorem congruentOne_single (v : Place K F) (n : ℕ) (f : F) :
    CongruentOne (Finsupp.single v n : Modulus K F) f ↔
      f ≠ 0 ∧ (n ≠ 0 → v.CongruentOne n f) := by
  classical
  constructor
  · intro h
    refine ⟨h.1, fun hn => ?_⟩
    simpa using h.2 v (by simpa using hn)
  · rintro ⟨hf, hv⟩
    refine ⟨hf, fun w hw => ?_⟩
    by_cases h : v = w
    · subst w
      simpa using hv (by simpa using hw)
    · simp [h] at hw

/-- Congruence-one rational functions form an actual subgroup of `Fˣ`. -/
def congruentOneSubgroup (D : Modulus K F) : Subgroup Fˣ where
  carrier := {u | D.CongruentOne (u : F)}
  one_mem' := CongruentOne.one D
  mul_mem' := fun hf hg => hf.mul hg
  inv_mem' := by
    intro u hf
    change D.CongruentOne ((u⁻¹ : Fˣ) : F)
    simpa only [Units.val_inv_eq_inv_val] using hf.inv

@[simp]
theorem mem_congruentOneSubgroup (D : Modulus K F) (u : Fˣ) :
    u ∈ D.congruentOneSubgroup ↔ D.CongruentOne (u : F) := Iff.rfl

end Modulus

end AlgebraicCurve

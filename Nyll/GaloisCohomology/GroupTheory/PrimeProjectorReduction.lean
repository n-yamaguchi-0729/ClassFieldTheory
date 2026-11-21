/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.GroupTheory.EquivariantPowerReduction
public import Nyll.GaloisCohomology.GroupTheory.PrimeProjectorWeight

/-! # The prime projector length of power reduction in a finite-index lattice -/

@[expose] public section

open Function
open scoped Ring

noncomputable section

namespace LinearMap

/-- Reduction by the original integral multiplication is annihilated by
that integer. -/
theorem nsmul_powerQuotient_eq_zero {R X : Type*} [CommRing R] [AddCommGroup X] [Module R X]
    (n : ℕ) (x : X ⧸ LinearMap.range (nsmulLinear (R := R) n X)) : n • x = 0 := by
  let V := LinearMap.range (nsmulLinear (R := R) n X)
  obtain ⟨y, rfl⟩ := V.mkQ_surjective x
  rw [← map_nsmul]
  exact (Submodule.Quotient.mk_eq_zero V).mpr ⟨y, rfl⟩

end LinearMap

namespace MonoidAlgebra

universe u v

variable {p : ℕ} (G : Type u) [CommGroup G] [Finite G]
  {J : Type v} [Fintype J] [DecidableEq J]
  (e : Matrix J J ((ZMod p)[G])) (he : IsIdempotentElem e) (hp : p.Prime)

/-- The prime valuation of the cardinality of the actual projected module. -/
def primeProjectorLength (X : ModuleCat.{u} ℤ[G]) [Finite X] : ℤ :=
  padicValNat p (primeProjectorCard (A := X) G e he hp)

private theorem primeProjectorCard_pos (X : ModuleCat.{u} ℤ[G]) [Finite X] :
    0 < primeProjectorCard (A := X) G e he hp := by
  unfold primeProjectorCard primeProjectorCardAt
  exact Nat.card_pos

theorem primeProjectorLength_add_of_exact (A B C : ModuleCat.{u} ℤ[G])
    [Finite A] [Finite B] [Finite C] (f : A →ₗ[ℤ[G]] B) (g : B →ₗ[ℤ[G]] C)
    (hf : Injective f) (hg : Surjective g) (hex : Exact f g) :
    primeProjectorLength G e he hp B =
      primeProjectorLength G e he hp A + primeProjectorLength G e he hp C := by
  let : Fact p.Prime := ⟨hp⟩
  unfold primeProjectorLength
  rw [primeProjectorCard_mul_of_exact G e he hp f g hf hg hex]
  simp only [Nat.padicValNat_def]
  rw [Nat.multiplicity_mul (primeProjectorCard_pos G e he hp A).ne'
    (primeProjectorCard_pos G e he hp C).ne', Nat.cast_add]

variable {A B C : Type u} [AddCommGroup A] [Module ℤ[G] A] [AddCommGroup B] [Module ℤ[G] B]
  [AddCommGroup C] [Module ℤ[G] C]

local notation "N[" X "]" => LinearMap.nsmulLinear (R := ℤ[G]) p X
local notation "Q[" X "]" => X ⧸ LinearMap.range (N[X])
local notation "T[" X "]" => LinearMap.ker (N[X])
local notation "V[" X "]" => primeProjectorLength G e he hp (ModuleCat.of ℤ[G] X)

/-- An integral lattice of finite index computes the actual projected
reduction, with the torsion of the original module as the correction. -/
theorem primeProjectorLength_powerReduction_of_finite_quotient (f : A →ₗ[ℤ[G]] B)
    (g : B →ₗ[ℤ[G]] C) (hf : Injective f) (hg : Surjective g) (hex : Exact f g)
    (hA : Injective (N[A])) [Finite C] [Finite (T[B])] [Finite (Q[A])] [Finite (Q[B])] :
    V[Q[B]] = V[Q[A]] + V[T[B]] :=
  LinearMap.powerReduction_value_of_finite_quotient (primeProjectorLength G e he hp)
    (primeProjectorLength_add_of_exact G e he hp) p f g hf hg hex hA

end MonoidAlgebra

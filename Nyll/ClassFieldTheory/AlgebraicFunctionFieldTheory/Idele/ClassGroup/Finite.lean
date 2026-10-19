/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Set.Finite.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Index.StichtenothGenusExists
import Nyll.AlgebraicCurves.Divisors.Degree.CardEffectiveDivisorsMulEqSum
import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup

/-!
# Finiteness of the degree-zero divisor class group

Over a finite full constant field, Riemann--Roch represents every degree-zero divisor class
by the difference of an effective divisor of one fixed degree and one fixed divisor. The
fixed divisor is a sufficiently large multiple of an arbitrary place, whose residue degree
is positive. No place of degree one is required.

The Riemann--Roch genus bound and finiteness of effective divisors are the existing curve
suppliers. The quotient is the existing `AlgebraicCurve.Pic0`, not a new class-group type.
-/

namespace AlgebraicCurve

variable (k K : Type*) [Field k] [Finite k] [Field K]
    [Algebra k K] [IsCurveOver k K] [Algebra.EssFiniteType k K]

/-- The degree-zero divisor class group is finite when the finite base is the full field of
constants. A place of arbitrary positive degree suffices for the Riemann--Roch argument. -/
theorem finite_pic0_of_isCurveOver (hC : ConstantsAreBase k K) : Finite (Pic0 k K) := by
  classical
  obtain ⟨⟨P⟩, _, γ, D₀, hγ⟩ := stichtenothGenusExists_of_isCurveOver hC
  have : Module.Finite k P.ResidueField := IsCurveOver.finiteResidue P
  have hP : 0 < P.deg := Module.finrank_pos (R := k) (M := P.ResidueField)
  let n : ℕ := γ.toNat + 1
  let m : ℕ := n * P.deg
  let B : Divisor k K := Finsupp.single P (n : ℤ)
  have hB : Divisor.degree B = (m : ℤ) := by
    change Divisor.degree (Finsupp.single P (n : ℤ)) = ((n * P.deg : ℕ) : ℤ)
    rw [Divisor.degree_single, Nat.cast_mul]
  have hγm : γ ≤ (m : ℤ) := by
    have hnm : n ≤ m := Nat.le_mul_of_pos_right n hP
    dsimp only [n] at hnm
    omega
  let S := {E : Divisor k K // 0 ≤ E ∧ Divisor.degree E = (m : ℤ)}
  have : Finite S := Set.finite_coe_iff.mpr
    (finite_effective_divisors (K := k) (F := K) m)
  let toClass : S → Pic0 k K := fun E => Pic0.mk ⟨E.1 - B, by
    change Divisor.degree (E.1 - B) = 0
    rw [map_sub, E.2.2, hB, sub_self]⟩
  apply Finite.of_surjective toClass
  intro c
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  let T : Divisor k K := (D : Divisor k K) + B
  have hT : Divisor.degree T = (m : ℤ) := by
    change Divisor.degree ((D : Divisor k K) + B) = (m : ℤ)
    rw [map_add, Divisor.mem_degZero.mp D.2, hB, zero_add]
  have hpos : 0 < Module.finrank k (LSpace T) := by
    have hmax := hγ.isMax T
    rw [hT] at hmax
    have hposInt : (0 : ℤ) < (ell T : ℤ) := by omega
    exact_mod_cast hposInt
  have hne : LSpace T ≠ ⊥ := by
    intro h
    rw [h, _root_.finrank_bot] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨f, hfT, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hord : ∀ v : Place k K, -T v ≤ v.ord f :=
    (mem_lSpace_iff_ord.mp hfT).resolve_left hf0
  obtain ⟨Df, hDf, hDfdeg⟩ := HasPrincipalDivisors.exists_divisor (K := k) f hf0
  have hE : 0 ≤ T + Df := by
    rw [Finsupp.le_def]
    intro v
    change 0 ≤ T v + Df v
    rw [hDf v]
    linarith [hord v]
  have hEdeg : Divisor.degree (T + Df) = (m : ℤ) := by
    rw [map_add, hT, hDfdeg, add_zero]
  refine ⟨⟨T + Df, hE, hEdeg⟩, ?_⟩
  change (QuotientAddGroup.mk ⟨T + Df - B, _⟩ : Pic0 k K) = QuotientAddGroup.mk D
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]
  change Divisor.IsPrincipal (T + Df - B - (D : Divisor k K))
  have heq : T + Df - B - (D : Divisor k K) = Df := by
    ext v
    change ((D : Divisor k K) v + B v) + Df v - B v -
      (D : Divisor k K) v = Df v
    omega
  rw [heq]
  exact ⟨f, hf0, hDf⟩

end AlgebraicCurve

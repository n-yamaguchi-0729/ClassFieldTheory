/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Tactic.Ring
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Adele.StrongApproximation
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.ArtinSchreierUnramified
import Nyll.AlgebraicCurves.Places.Completion
import Nyll.GaloisCohomology.ArtinSchreier.FiniteExtension
import Nyll.ValuedFieldTheory.Valuation.Henselian.ArtinSchreier
import Nyll.ValuedFieldTheory.Valuation.ValuedAdicComplete

/-!
# Artin–Schreier approximation with controlled ramification support

Strong approximation supplies a global parameter in the prescribed local
Artin–Schreier classes and integral outside those places and one allowed pole.
Adjoining a root constructs an actual finite cyclic extension inside the fixed
overfield. Its ramification is confined to that same specified finite set.
No condition is imposed at the one auxiliary place.
-/

open scoped WithZero
noncomputable section

namespace FunctionField

open AlgebraicCurve

variable {k K Ω : Type*} [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [IsSepClosed Ω]

/-- Prescribed local Artin–Schreier classes are realized by an actual finite
cyclic extension unramified outside the prescribed places and one allowed pole. -/
theorem exists_artinSchreier_extension_unramified_away
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (S : Finset (Place k K)) (x : ∀ v : Place k K, v.adicCompletion)
    (v₀ : Place k K) (hv₀ : v₀ ∉ S) :
    ∃ a : K, ∃ E : FiniteGaloisIntermediateField K Ω,
      IsCyclic Gal(E/K) ∧ ∃ β : E,
        β ^ p - β = algebraMap K E a ∧ Algebra.adjoin K {β} = ⊤ ∧
        (∀ v ∈ S, ∃ b : v.adicCompletion,
          b ^ p - b = x v - algebraMap K v.adicCompletion a) ∧
        (∀ w : Place k E, w.restrict K ∉ S → w.restrict K ≠ v₀ →
          w.ramificationIndex K = 1) := by
  obtain ⟨a, hlocal, haway⟩ :=
    AdeleRing.exists_approx_integral_away S x (fun _ => -1) v₀ hv₀
  have hclasses (v : Place k K) (hv : v ∈ S) :
      ∃ b : v.adicCompletion, b ^ p - b = x v - algebraMap K v.adicCompletion a := by
    have hchar : CharP v.adicCompletion p :=
      charP_of_injective_algebraMap (algebraMap K v.adicCompletion).injective p
    have hcomplete : ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete
        (Valued.v : Valuation v.adicCompletion ℤᵐ⁰) :=
      (ValuationTheory.Valuations.completeDVFOfCompleteValuedField
        (K := v.adicCompletion) (Gamma := ℤᵐ⁰)).instCompleteDiscrete
    have hhenselian : HenselianRing
        (Valued.v : Valuation v.adicCompletion ℤᵐ⁰).valuationSubring
        (IsLocalRing.maximalIdeal
          (Valued.v : Valuation v.adicCompletion ℤᵐ⁰).valuationSubring) :=
      ValuationTheory.DiscreteValuationField.Valuation.henselianRing
        (Valued.v : Valuation v.adicCompletion ℤᵐ⁰)
    apply ValuationTheory.exists_pow_sub_eq_of_valuation_lt_one Valued.v p
    exact (hlocal v hv).trans_lt
      (WithZero.exp_lt_one_iff.mpr (by decide : (-1 : ℤ) < 0))
  obtain ⟨E, hcyclic, β, hβ, hgen⟩ :=
    ArtinSchreierTheory.exists_finite_cyclic_extension p K Ω a
  refine ⟨a, E, hcyclic, β, hβ, hgen, hclasses, ?_⟩
  intro w hwS hw₀
  apply artinSchreier_ramificationIndex_eq_one p a β hβ hgen w
  exact (algebraMap_mem_adicCompletionIntegers_iff (w.restrict K) a).mp
    (haway (w.restrict K) hwS hw₀)

/-- If one prescribed local class is nonzero, the supported cyclic extension
has degree exactly `p`, while retaining all local classes and ramification bounds. -/
theorem exists_artinSchreier_extension_degree_prime_unramified_away
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (S : Finset (Place k K)) (x : ∀ v : Place k K, v.adicCompletion)
    (v₀ : Place k K) (hv₀ : v₀ ∉ S)
    (hx : ∃ v ∈ S, ∀ b : v.adicCompletion, b ^ p - b ≠ x v) :
    ∃ a : K, ∃ E : FiniteGaloisIntermediateField K Ω,
      IsCyclic Gal(E/K) ∧ Module.finrank K E = p ∧ ∃ β : E,
        β ^ p - β = algebraMap K E a ∧ Algebra.adjoin K {β} = ⊤ ∧
        (∀ v ∈ S, ∃ b : v.adicCompletion,
          b ^ p - b = x v - algebraMap K v.adicCompletion a) ∧
        (∀ w : Place k E, w.restrict K ∉ S → w.restrict K ≠ v₀ →
          w.ramificationIndex K = 1) := by
  obtain ⟨a, E, hcyclic, β, hβ, hgen, hclasses, haway⟩ :=
    exists_artinSchreier_extension_unramified_away (Ω := Ω) p S x v₀ hv₀
  obtain ⟨v, hv, hx⟩ := hx
  have hcharv : CharP v.adicCompletion p :=
    charP_of_injective_algebraMap (algebraMap K v.adicCompletion).injective p
  obtain ⟨z, hz⟩ := hclasses v hv
  have ha : ∀ t : K, t ^ p - t ≠ a := by
    intro t ht
    apply hx (z + algebraMap K v.adicCompletion t)
    have htlocal : (algebraMap K v.adicCompletion t) ^ p -
        algebraMap K v.adicCompletion t = algebraMap K v.adicCompletion a := by
      rw [← map_pow, ← map_sub, ht]
    rw [add_pow_char]
    calc
      z ^ p + (algebraMap K v.adicCompletion t) ^ p -
          (z + algebraMap K v.adicCompletion t) =
          (z ^ p - z) + ((algebraMap K v.adicCompletion t) ^ p -
            algebraMap K v.adicCompletion t) := by ring
      _ = x v := by rw [hz, htlocal, sub_add_cancel]
  have hcharE : CharP E p := (Algebra.charP_iff K E p).mp inferInstance
  have hdegree : Module.finrank K E = p :=
    ArtinSchreierTheory.finrank_eq_prime_of_adjoin_eq_top_of_no_root p a β hβ hgen ha
  exact ⟨a, E, hcyclic, hdegree, β, hβ, hgen, hclasses, haway⟩

end FunctionField

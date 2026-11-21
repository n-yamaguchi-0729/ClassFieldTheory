/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.Ramification.Different.TracePower
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension

/-!
# Exact trace preimages at nonnegative local depths

This is the integral-element form of the fractional-ideal trace formula.
All integral-closure and finite-module data come from the actual local extension.
-/

@[expose] public section

noncomputable section

namespace LocalFieldTheory

universe u v

open scoped ValuativeRel nonZeroDivisors

variable (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

/-- At the floor depth determined by the actual different and ramification
index, every integral target has a trace preimage in the specified source power. -/
theorem exists_trace_mem_maximalIdeal_pow_iff (m r : ℕ)
    (hr : (r : ℤ) =
      ((m : ℤ) + FractionalIdeal.count L
        (RamificationTheory.DiscreteValuationRing.maximalSpectrum 𝒪[L])
        (differentIdeal 𝒪[K] 𝒪[L] : FractionalIdeal (𝒪[L])⁰ L)) /
          ((𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] : ℤ)) (a : K) :
    (∃ x : 𝒪[L], x ∈ (𝓂[L] ^ m : Ideal 𝒪[L]) ∧ Algebra.trace K L (x : L) = a) ↔
      ∃ y : 𝒪[K], y ∈ (𝓂[K] ^ r : Ideal 𝒪[K]) ∧ (y : K) = a := by
  let : IsIntegralClosure 𝒪[L] 𝒪[K] L := localCompleteDVF_integerRing_isIntegralClosure K L
  let : Module.Finite 𝒪[K] 𝒪[L] := localCompleteDVF_integerRing_moduleFinite K L
  let : Algebra.IsIntegral 𝒪[K] 𝒪[L] :=
    integerRing_algebra_isIntegral_of_isIntegralClosure K L
  let : FaithfulSMul 𝒪[K] 𝒪[L] :=
    FaithfulSMul.of_field_isFractionRing 𝒪[K] 𝒪[L] K L
  have h := RamificationTheory.DiscreteValuationRing.traceImage_maximalIdeal_zpow_count
    𝒪[K] K 𝒪[L] L (m : ℤ)
  rw [← hr, zpow_natCast, zpow_natCast, ← FractionalIdeal.coeIdeal_pow,
    ← FractionalIdeal.coeIdeal_pow] at h
  constructor
  · rintro ⟨x, hx, hxa⟩
    have ht : a ∈ FractionalIdeal.traceImage 𝒪[K] K
        ((𝓂[L] ^ m : Ideal 𝒪[L]) : FractionalIdeal (𝒪[L])⁰ L) :=
      (FractionalIdeal.mem_traceImage 𝒪[K] K _ a).mpr
        ⟨(x : L), (FractionalIdeal.mem_coeIdeal (𝒪[L])⁰).mpr ⟨x, hx, rfl⟩, hxa⟩
    rw [h] at ht
    exact (FractionalIdeal.mem_coeIdeal (𝒪[K])⁰).mp ht
  · rintro ⟨y, hy, hya⟩
    have ht : a ∈ ((𝓂[K] ^ r : Ideal 𝒪[K]) : FractionalIdeal (𝒪[K])⁰ K) :=
      (FractionalIdeal.mem_coeIdeal (𝒪[K])⁰).mpr ⟨y, hy, hya⟩
    rw [← h] at ht
    obtain ⟨z, hz, hza⟩ := (FractionalIdeal.mem_traceImage 𝒪[K] K _ a).mp ht
    obtain ⟨x, hx, hxz⟩ := (FractionalIdeal.mem_coeIdeal (𝒪[L])⁰).mp hz
    exact ⟨x, hx, (congrArg (Algebra.trace K L) hxz).trans hza⟩

end LocalFieldTheory

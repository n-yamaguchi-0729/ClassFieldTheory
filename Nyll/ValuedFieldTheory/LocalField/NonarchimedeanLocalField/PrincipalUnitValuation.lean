/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Lean.Elab.Tactic.Omega
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnitTopology
public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CyclicValueGroup
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
public import Nyll.ValuedFieldTheory.Valuation.LocalRingEquiv

/-!
# Principal units measured by a normalized discrete valuation

A compatible surjective integer valuation measures every positive
principal-unit level. This comparison needs no finite residue field or
local compactness and applies to completions of arbitrary curve places.
-/

@[expose] public section

noncomputable section

universe u

namespace LocalFieldTheory

open scoped ValuativeRel
open LocalFieldTheory.IsNonarchimedeanLocalField
open DiscreteValuationField.WithZeroValuation
open ValuationTheory.DiscreteValuationField.Valuation

variable (F : Type u) [Field F] [ValuativeRel F]
  (ν : Valuation F (WithZero (Multiplicative ℤ))) [ν.Compatible] [ν.IsRankOneDiscrete]
  (hν : Function.Surjective ν)

include hν

/-- The integer-unit filtration is measured by any compatible normalized integer valuation. -/
theorem mem_principalUnits_iff_valuation_sub_one_le (a : 𝒪[F]ˣ) (n : ℕ) :
    a ∈ principalUnits F n ↔
      ν (((a : 𝒪[F]) : F) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  let e : 𝒪[F] ≃+* ν.valuationSubring := RingEquiv.subringCongr
    (congrArg ValuationSubring.toSubring
      ((Valuation.isEquiv_iff_valuationSubring (ValuativeRel.valuation F) ν).mp
        (ValuativeRel.isEquiv (ValuativeRel.valuation F) ν)))
  obtain ⟨π, hπ⟩ := exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective ν hν
  have hπu :=
    DiscreteValuationField.WithZeroValuation.isUniformizer_of_valuation_eq_exp_neg_one ν (π : F) hπ
  change (a : 𝒪[F]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[F] ^ n ↔ _
  rw [← ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff e n ((a : 𝒪[F]) - 1),
    mem_maximalIdeal_pow_iff_valuation_le_uniformizer_pow ν hπu n]
  change ν (((a : 𝒪[F]) : F) - 1) ≤ ν ((π : F) ^ n) ↔ _
  rw [map_pow, hπ, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg_one]

/-- At positive depth, the same valuation inequality characterizes the actual
principal-unit subgroup inside the field multiplicative group. -/
theorem mem_fieldPrincipalUnits_iff_valuation_sub_one_le
    (x : Fˣ) {n : ℕ} (hn : 1 ≤ n) :
    x ∈ fieldPrincipalUnits F n ↔ ν ((x : F) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (mem_principalUnits_iff_valuation_sub_one_le F ν hν a n).mp ha
  · intro hx
    have hsmall : ν ((x : F) - 1) < 1 := by
      apply lt_of_le_of_lt hx
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have hval : ν (x : F) = 1 := by
      have h := ν.map_eq_of_sub_lt (show ν ((x : F) - 1) < ν 1 by
        rw [map_one]
        exact hsmall)
      exact h.trans (map_one ν)
    have hintrinsic : ValuativeRel.valuation F (x : F) = 1 :=
      (ValuativeRel.isEquiv (ValuativeRel.valuation F) ν).eq_one_iff_eq_one.mpr hval
    obtain ⟨a, ha⟩ :=
      (mem_localBaseUnitSubgroup_iff_valuation_eq_one F x).mpr hintrinsic
    refine ⟨a, (mem_principalUnits_iff_valuation_sub_one_le F ν hν a n).mpr ?_, ha⟩
    have hcoe : ((a : 𝒪[F]) : F) = (x : F) := congrArg Units.val ha
    rw [hcoe]
    exact hx

end LocalFieldTheory

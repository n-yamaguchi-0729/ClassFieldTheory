/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
public import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLog
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationExtensionContinuous
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# The actual mixed-characteristic logarithm under field extensions

Continuity of the extension map and convergence of the existing series prove
embedding naturality. No logarithm comparison is supplied as an assumption,
and the normalization of the two discrete valuations may differ.
-/

@[expose] public section

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L]
    [CharZero K] [CharZero L] [Algebra K L]

/-- The convergent logarithm series commutes with a discrete valued extension. -/
theorem map_logOnePlusSeriesField_of_hasExtension
    (vK : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (vL : _root_.Valuation L (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vK]
    [vL.IsRankOneDiscrete] [vK.HasExtension vL]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField vK.valuationSubring) p]
    (x : K) (hx : vK x < 1) :
    algebraMap K L (logOnePlusSeriesFieldOfWithZeroValuation vK x
      (fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))) =
      logOnePlusSeriesFieldOfWithZeroValuation vL (algebraMap K L x)
        (fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' vK
  let : Valued L (WithZero (Multiplicative ℤ)) := Valued.mk' vL
  have hs :=
    hasSum_signedLogSeriesTermField_logOnePlusSeriesField_ofWithZeroValuation_scaled_of_lt_one
      vK (p := p) (vK.residueRamificationIndex p) x
      (fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
      (fun n => vK.natCast_eq_exp_neg_ramificationIndex_mul_padicValNat p
        (n + 1) (Nat.succ_ne_zero n)) hx
      (ValuationTheory.DiscreteValuationField.Valuation.completeSpace_ofWithZeroValuation vK)
  have hm := hs.map (algebraMap K L).toAddMonoidHom
    (ValuationTheory.DiscreteValuationField.Valuation.continuous_algebraMap_of_hasExtension
      vK vL)
  change HasSum
    (fun n : ℕ => algebraMap K L (signedLogSeriesTermField x
      (fun j => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)) n))
    (algebraMap K L (logOnePlusSeriesFieldOfWithZeroValuation vK x
      (fun j => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)))) at hm
  have ht : HasSum
      (fun n : ℕ => signedLogSeriesTermField (algebraMap K L x)
        (fun j => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)) n)
      (algebraMap K L (logOnePlusSeriesFieldOfWithZeroValuation vK x
        (fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)))) := by
    simpa only [signedLogSeriesTermField, logSeriesTermField, Units.val_mk0,
      map_mul, map_pow, map_neg, map_one, map_div₀, map_natCast] using hm
  exact ht.tsum_eq.symm

/-- Naturality on the existing principal-unit groups, stated using the actual
field values so it applies to any representative-preserving extension map. -/
theorem principalUnitLogOfMixedChar_map_of_hasExtension
    (vK : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (vL : _root_.Valuation L (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vK]
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vL]
    [vK.HasExtension vL]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField vK.valuationSubring) p]
    [CharP (IsLocalRing.ResidueField vL.valuationSubring) p]
    (a : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation vK) 1)
    (b : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation vL) 1)
    (hab : algebraMap K L (a.1.val : K) = (b.1.val : L)) :
    algebraMap K L (principalUnitLogOfMixedChar vK p a).toAdd =
      (principalUnitLogOfMixedChar vL p b).toAdd := by
  rw [principalUnitLogOfMixedChar_apply_toAdd, principalUnitLogOfMixedChar_apply_toAdd]
  simp only [principalUnitLogSeriesOfWithZeroValuation]
  rw [map_logOnePlusSeriesField_of_hasExtension vK vL p
    (principalUnitSubOneOfWithZeroValuation vK a)
    (principalUnitSubOne_val_lt_one_ofWithZeroValuation vK a)]
  congr 1
  simpa only [principalUnitSubOneOfWithZeroValuation, map_sub, map_one] using
    congrArg (fun z : L => z - 1) hab

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.LocalField.Analytic.PrincipalUnitExpLogValues
public import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLogNorm
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormalizedPrincipalUnits
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparablePrincipalUnitNorm
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.TracePrincipalIdeal
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Exact images of sufficiently deep principal-unit norms

The existing exponential–logarithm equivalence is transported to the standard
principal units and integer ideals. Its actual logarithm identifies the field
norm with the field trace, whose image is determined by the actual different.
-/

@[expose] public section

noncomputable section

namespace LocalFieldTheory

universe u v

open scoped ValuativeRel nonZeroDivisors
open DiscreteValuationField.MultiplicativeIntegerValuation

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K]

/-- The strict exponential threshold for the canonical normalized valuation.
At the boundary the logarithm can have a torsion kernel. -/
def localLogExpThreshold : ℚ :=
  (DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation
      (localIntegerValuation K) : ℚ) /
    (((DiscreteValuationField.LocalField.ofWithZeroValuation
      (localIntegerValuation K)).residueCharacteristic : ℚ) - 1)

/-- The mixed-characteristic exponential threshold is positive. -/
theorem localLogExpThreshold_pos : 0 < localLogExpThreshold K := by
  apply div_pos
  · exact_mod_cast
      DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation_pos
        (localIntegerValuation K)
  · apply sub_pos.mpr
    exact_mod_cast
      (DiscreteValuationField.LocalField.ofWithZeroValuation
        (localIntegerValuation K)).residueCharacteristic_prime.one_lt

/-- The existing deep logarithm on the standard field-unit subgroup and the
actual maximal-ideal power, preserving their original carriers. -/
def fieldPrincipalUnitsLogMulEquiv (n : ℕ) (hn : localLogExpThreshold K < (n : ℚ)) :
    fieldPrincipalUnits K n ≃* Multiplicative (𝓂[K] ^ n : Ideal 𝒪[K]) :=
  (localIntegerValuationPrincipalUnitsEquiv K n).symm.trans
    ((Padic.expLogMulEquivOfWithZeroValuation (localIntegerValuation K)
      (localIntegerValuation_surjective K) n hn).symm.trans
        (localIntegerValuationIdealPowEquiv K n).toMultiplicative)

/-- The transported deep logarithm is the original convergent log series. -/
theorem fieldPrincipalUnitsLogMulEquiv_fieldVal
    (n : ℕ) (hn : localLogExpThreshold K < (n : ℚ)) (a : fieldPrincipalUnits K n) :
    ((((fieldPrincipalUnitsLogMulEquiv K n hn a).toAdd : 𝒪[K]) : K)) =
      logOnePlusSeriesFieldOfWithZeroValuation (localIntegerValuation K)
        (((a : Kˣ) : K) - 1)
        (fun j => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)) := by
  let v := localIntegerValuation K
  have hlevel : (DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation v : ℚ) /
      (((DiscreteValuationField.LocalField.ofWithZeroValuation v).residueCharacteristic : ℚ) - 1) <
        (n : ℚ) := hn
  let u := (localIntegerValuationPrincipalUnitsEquiv K n).symm a
  let b := ((Padic.expLogMulEquivOfWithZeroValuation v
    (localIntegerValuation_surjective K) n hlevel).symm u).toAdd
  calc
    _ = (b.1 : K) := localIntegerValuationIdealPowEquiv_apply_coe K n b
    _ = logOnePlusSeriesFieldOfWithZeroValuation v ((u.1.val : K) - 1)
        (fun j => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)) :=
      Padic.expLogMulEquivOfWithZeroValuation_symm_fieldVal v
        (localIntegerValuation_surjective K) n hlevel u
    _ = _ := congrArg (fun z : K => logOnePlusSeriesFieldOfWithZeroValuation v (z - 1)
      (fun j => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)))
      (localIntegerValuationPrincipalUnitsEquiv_symm_apply_coe K n a)

/-- The inverse deep logarithm realizes its additive input by the same series. -/
theorem fieldPrincipalUnitsLogMulEquiv_symm_fieldVal
    (n : ℕ) (hn : localLogExpThreshold K < (n : ℚ))
    (x : Multiplicative (𝓂[K] ^ n : Ideal 𝒪[K])) :
    logOnePlusSeriesFieldOfWithZeroValuation (localIntegerValuation K)
        (((((fieldPrincipalUnitsLogMulEquiv K n hn).symm x) : Kˣ) : K) - 1)
        (fun j => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)) =
      ((x.toAdd : 𝒪[K]) : K) := by
  rw [← fieldPrincipalUnitsLogMulEquiv_fieldVal K n hn
    ((fieldPrincipalUnitsLogMulEquiv K n hn).symm x),
    MulEquiv.apply_symm_apply]

/-- The same series is injective on every strict deep principal-unit domain. -/
theorem fieldPrincipalUnits_log_injective
    (n : ℕ) (hn : localLogExpThreshold K < (n : ℚ))
    {a b : Kˣ} (ha : a ∈ fieldPrincipalUnits K n) (hb : b ∈ fieldPrincipalUnits K n)
    (hab : logOnePlusSeriesFieldOfWithZeroValuation (localIntegerValuation K) ((a : K) - 1)
        (fun j => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)) =
      logOnePlusSeriesFieldOfWithZeroValuation (localIntegerValuation K) ((b : K) - 1)
        (fun j => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j))) : a = b := by
  have he : fieldPrincipalUnitsLogMulEquiv K n hn ⟨a, ha⟩ =
      fieldPrincipalUnitsLogMulEquiv K n hn ⟨b, hb⟩ := by
    apply Multiplicative.ext
    apply Subtype.ext
    apply Subtype.ext
    rw [fieldPrincipalUnitsLogMulEquiv_fieldVal, fieldPrincipalUnitsLogMulEquiv_fieldVal]
    exact hab
  exact congrArg Subtype.val ((fieldPrincipalUnitsLogMulEquiv K n hn).injective he)

omit [CharZero K] in
private theorem sub_one_lt_one_of_mem_fieldPrincipalUnits
    {n : ℕ} (hn : 1 ≤ n) {a : Kˣ} (ha : a ∈ fieldPrincipalUnits K n) :
    localIntegerValuation K ((a : K) - 1) < 1 := by
  have ha₁ : a ∈ fieldPrincipalUnits K 1 :=
    Subgroup.map_mono (principalUnits_antitone K hn) ha
  let b := (localIntegerValuationPrincipalUnitsEquiv K 1).symm ⟨a, ha₁⟩
  have h := principalUnitSubOne_val_lt_one_ofWithZeroValuation (localIntegerValuation K) b
  change localIntegerValuation K ((b.1.val : K) - 1) < 1 at h
  dsimp only [b] at h
  rw [localIntegerValuationPrincipalUnitsEquiv_symm_apply_coe] at h
  exact h

variable (L : Type v) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [CharZero L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

/-- The actual standard field-unit norm satisfies the logarithm–trace identity
for every finite separable mixed-characteristic local extension. -/
theorem fieldPrincipalUnits_log_norm {m : ℕ} (hm : 1 ≤ m)
    {a : Lˣ} (ha : a ∈ fieldPrincipalUnits L m) :
    logOnePlusSeriesFieldOfWithZeroValuation (localIntegerValuation K)
        (((normUnits K L a : Kˣ) : K) - 1)
        (fun j => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)) =
      Algebra.trace K L (logOnePlusSeriesFieldOfWithZeroValuation (localIntegerValuation L)
        ((a : L) - 1) (fun j => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j))) := by
  let : (localIntegerValuation K).HasExtension (localIntegerValuation L) :=
    localIntegerValuation_hasExtension K L
  let p := (DiscreteValuationField.LocalField.ofWithZeroValuation
    (localIntegerValuation K)).residueCharacteristic
  let : Fact p.Prime :=
    ⟨(DiscreteValuationField.LocalField.ofWithZeroValuation
      (localIntegerValuation K)).residueCharacteristic_prime⟩
  let : CharP (IsLocalRing.ResidueField (localIntegerValuation K).valuationSubring) p := by
    dsimp only [p]
    infer_instance
  let : CharP (IsLocalRing.ResidueField (localIntegerValuation L).valuationSubring) p :=
    (Algebra.charP_iff
      (IsLocalRing.ResidueField (localIntegerValuation K).valuationSubring)
      (IsLocalRing.ResidueField (localIntegerValuation L).valuationSubring) p).mp inferInstance
  exact logOnePlusSeriesField_norm_eq_trace (localIntegerValuation K)
    (localIntegerValuation L) p (a : L)
    (sub_one_lt_one_of_mem_fieldPrincipalUnits L hm ha)

/-- At a source depth above the exponential threshold, the actual norm image
is the exact trace depth. The auxiliary depth `t` exhibits a strict domain of
logarithmic injectivity for all norm values, using the proved safe norm bound.
All three depth conditions are explicit numerical inequalities. -/
theorem fieldPrincipalUnits_norm_eq_of_deep (m r t : ℕ)
    (hm : localLogExpThreshold L < (m : ℚ))
    (ht : localLogExpThreshold K < (t : ℚ)) (htr : t ≤ r)
    (hsafe : (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] * (t - 1) < m)
    (hr : (r : ℤ) =
      ((m : ℤ) + FractionalIdeal.count L
        (RamificationTheory.DiscreteValuationRing.maximalSpectrum 𝒪[L])
        (differentIdeal 𝒪[K] 𝒪[L] : FractionalIdeal (𝒪[L])⁰ L)) /
          ((𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] : ℤ)) :
    (fieldPrincipalUnits L m).map (normUnits K L) = fieldPrincipalUnits K r := by
  have hrdeep : localLogExpThreshold K < (r : ℚ) :=
    lt_of_lt_of_le ht (by exact_mod_cast htr)
  have hm₁ : 1 ≤ m := by
    have hpos : (0 : ℚ) < (m : ℚ) := lt_trans (localLogExpThreshold_pos L) hm
    exact_mod_cast hpos
  have hnorm : fieldPrincipalUnits L m ≤
      (fieldPrincipalUnits K t).comap (normUnits K L) :=
    fieldPrincipalUnits_le_norm_preimage_of_isSeparable K L hsafe
  have hrle : fieldPrincipalUnits K r ≤ fieldPrincipalUnits K t :=
    Subgroup.map_mono (principalUnits_antitone K htr)
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    let z := (fieldPrincipalUnitsLogMulEquiv L m hm ⟨a, ha⟩).toAdd
    obtain ⟨y, hy, hyz⟩ := (exists_trace_mem_maximalIdeal_pow_iff K L m r hr
      (Algebra.trace K L ((z : 𝒪[L]) : L))).mp ⟨z, z.property, rfl⟩
    let c := (fieldPrincipalUnitsLogMulEquiv K r hrdeep).symm
      (Multiplicative.ofAdd ⟨y, hy⟩)
    have hlog :
        logOnePlusSeriesFieldOfWithZeroValuation (localIntegerValuation K)
            (((normUnits K L a : Kˣ) : K) - 1)
            (fun j => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)) =
          logOnePlusSeriesFieldOfWithZeroValuation (localIntegerValuation K)
            (((c : Kˣ) : K) - 1)
            (fun j => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)) := by
      calc
        _ = Algebra.trace K L (logOnePlusSeriesFieldOfWithZeroValuation
              (localIntegerValuation L) ((a : L) - 1)
              (fun j => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j))) :=
          fieldPrincipalUnits_log_norm K L hm₁ ha
        _ = Algebra.trace K L ((z : 𝒪[L]) : L) :=
          congrArg (Algebra.trace K L)
            (fieldPrincipalUnitsLogMulEquiv_fieldVal L m hm ⟨a, ha⟩).symm
        _ = (y : K) := hyz.symm
        _ = _ := (fieldPrincipalUnitsLogMulEquiv_symm_fieldVal K r hrdeep
          (Multiplicative.ofAdd ⟨y, hy⟩)).symm
    have heq := fieldPrincipalUnits_log_injective K t ht
      (hnorm ha) (hrle c.property) hlog
    rw [heq]
    exact c.property
  · intro hb
    let z := (fieldPrincipalUnitsLogMulEquiv K r hrdeep ⟨b, hb⟩).toAdd
    obtain ⟨y, hy, hyz⟩ := (exists_trace_mem_maximalIdeal_pow_iff K L m r hr
      ((z : 𝒪[K]) : K)).mpr ⟨z, z.property, rfl⟩
    let a := (fieldPrincipalUnitsLogMulEquiv L m hm).symm
      (Multiplicative.ofAdd ⟨y, hy⟩)
    refine ⟨(a : Lˣ), a.property, ?_⟩
    apply fieldPrincipalUnits_log_injective K t ht (hnorm a.property) (hrle hb)
    calc
      _ = Algebra.trace K L (logOnePlusSeriesFieldOfWithZeroValuation
            (localIntegerValuation L) (((a : Lˣ) : L) - 1)
            (fun j => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j))) :=
        fieldPrincipalUnits_log_norm K L hm₁ a.property
      _ = Algebra.trace K L (y : L) := congrArg (Algebra.trace K L)
        (fieldPrincipalUnitsLogMulEquiv_symm_fieldVal L m hm
          (Multiplicative.ofAdd ⟨y, hy⟩))
      _ = ((z : 𝒪[K]) : K) := hyz
      _ = _ := fieldPrincipalUnitsLogMulEquiv_fieldVal K r hrdeep ⟨b, hb⟩

/-- Every finite separable mixed-characteristic local extension has an eventual
exact norm-image formula. Both exponential domains and the safe norm depth are
derived by choosing one sufficiently large source bound. The exponent uses
the actual different and ramification index, with no Galois or tame assumption. -/
theorem exists_fieldPrincipalUnits_norm_eq_of_large :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      (fieldPrincipalUnits L m).map (normUnits K L) =
        fieldPrincipalUnits K
          ((((m : ℤ) + FractionalIdeal.count L
            (RamificationTheory.DiscreteValuationRing.maximalSpectrum 𝒪[L])
            (differentIdeal 𝒪[K] 𝒪[L] : FractionalIdeal (𝒪[L])⁰ L)) /
              ((𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] : ℤ)).toNat) := by
  let : IsIntegralClosure 𝒪[L] 𝒪[K] L := localCompleteDVF_integerRing_isIntegralClosure K L
  let : Module.Finite 𝒪[K] 𝒪[L] := localCompleteDVF_integerRing_moduleFinite K L
  let : Algebra.IsIntegral 𝒪[K] 𝒪[L] :=
    integerRing_algebra_isIntegral_of_isIntegralClosure K L
  let : FaithfulSMul 𝒪[K] 𝒪[L] :=
    FaithfulSMul.of_field_isFractionRing 𝒪[K] 𝒪[L] K L
  let d := FractionalIdeal.count L
    (RamificationTheory.DiscreteValuationRing.maximalSpectrum 𝒪[L])
    (differentIdeal 𝒪[K] 𝒪[L] : FractionalIdeal (𝒪[L])⁰ L)
  let e := (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K]
  have he : 0 < e := Ideal.ramificationIdx_pos 𝒪[K] (𝓂[L] : Ideal 𝒪[L])
  have hd : 0 ≤ d := by
    have hD : (differentIdeal 𝒪[K] 𝒪[L] : FractionalIdeal (𝒪[L])⁰ L) ≠ 0 := by
      rw [coeIdeal_differentIdeal 𝒪[K] K L 𝒪[L]]
      exact inv_ne_zero (FractionalIdeal.dual_ne_zero 𝒪[K] K one_ne_zero)
    have hrepr := RamificationTheory.DiscreteValuationRing.fractionalIdeal_eq_maximalIdeal_zpow
      𝒪[L] L hD
    apply (RamificationTheory.DiscreteValuationRing.maximalIdeal_zpow_le_iff
      𝒪[L] L d 0).mp
    rw [zpow_zero, ← hrepr]
    exact FractionalIdeal.coeIdeal_le_one
  obtain ⟨t, ht⟩ := exists_nat_gt (localLogExpThreshold K)
  obtain ⟨n, hn⟩ := exists_nat_gt (localLogExpThreshold L)
  have htpos : 0 < t := by
    have hpos : (0 : ℚ) < (t : ℚ) := lt_trans (localLogExpThreshold_pos K) ht
    exact_mod_cast hpos
  refine ⟨max n (e * t), ?_⟩
  intro m hm
  have hnm : n ≤ m := le_trans (le_max_left n (e * t)) hm
  have hem : e * t ≤ m := le_trans (le_max_right n (e * t)) hm
  let r : ℕ := (((m : ℤ) + d) / (e : ℤ)).toNat
  have heZ : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
  have hr : (r : ℤ) = ((m : ℤ) + d) / (e : ℤ) :=
    Int.toNat_of_nonneg (Int.ediv_nonneg (add_nonneg (Int.natCast_nonneg m) hd) heZ.le)
  have htr : t ≤ r := by
    apply Int.ofNat_le.mp
    rw [hr, Int.le_ediv_iff_mul_le heZ]
    have hemZ : (e : ℤ) * (t : ℤ) ≤ (m : ℤ) := by exact_mod_cast hem
    rw [mul_comm]
    exact le_trans hemZ (le_add_of_nonneg_right hd)
  have hsafe : e * (t - 1) < m :=
    lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_left (Nat.sub_lt htpos Nat.zero_lt_one) he) hem
  exact fieldPrincipalUnits_norm_eq_of_deep K L m r t
    (lt_of_lt_of_le hn (by exact_mod_cast hnm)) ht htr hsafe hr

end LocalFieldTheory

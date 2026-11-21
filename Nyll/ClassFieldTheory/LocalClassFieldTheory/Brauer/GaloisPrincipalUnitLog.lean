/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.DeepPrincipalUnitNorm
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic

/-! # Galois equivariance of the deep principal-unit logarithm -/

@[expose] public section

open scoped ValuativeRel
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

noncomputable section

namespace ClassFieldTheory.Brauer

universe u v

variable (K : Type u) (L : Type v) [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [CharZero L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]

/-- The actual deep logarithm on units of the valuation integer ring. -/
def integerPrincipalUnitsLogEquiv (r : ℕ) (hr : localLogExpThreshold L < (r : ℚ)) :
    Additive (principalUnits L r) ≃+ (𝓂[L] ^ r : Ideal 𝒪[L]) :=
  (((principalUnits L r).equivMapOfInjective (integerUnitsToFieldUnits L)
    (integerUnitsToFieldUnits_injective L)).trans
      (fieldPrincipalUnitsLogMulEquiv L r hr)).toAdditive

omit [CharZero L] in
private theorem localIntegerValuation_integer_eq :
    (localIntegerValuation L).integer = 𝒪[L] := by
  change (localIntegerValuation L).valuationSubring.toSubring = 𝒪[L]
  rw [localIntegerValuation_valuationSubring_eq, localCompleteDVF_valuation_eq]
  rfl

private theorem logOnePlusSeriesField_galois (σ : Gal(L/K)) (x : L)
    (hx : localIntegerValuation L x < 1) :
    σ (logOnePlusSeriesFieldOfWithZeroValuation (localIntegerValuation L) x
        (fun j => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j))) =
      logOnePlusSeriesFieldOfWithZeroValuation (localIntegerValuation L) (σ x)
        (fun j => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)) := by
  let : Algebra L L := σ.toRingHom.toAlgebra
  let v := localIntegerValuation L
  let : v.HasExtension v := by
    apply Valuation.HasExtension.ofComapInteger
    change v.integer.comap σ.toRingHom = v.integer
    rw [localIntegerValuation_integer_eq L]
    ext y
    change σ y ∈ 𝒪[L] ↔ y ∈ 𝒪[L]
    constructor
    · intro hy
      have h := galoisGroup_mem_integerRing_of_isIntegralClosure K L σ.symm ⟨σ y, hy⟩
      simpa only [AlgEquiv.symm_apply_apply] using h
    · intro hy
      exact galoisGroup_mem_integerRing_of_isIntegralClosure K L σ ⟨y, hy⟩
  let F := DiscreteValuationField.LocalField.ofWithZeroValuation v
  let p := F.residueCharacteristic
  let : Fact p.Prime := ⟨F.residueCharacteristic_prime⟩
  let : CharP (IsLocalRing.ResidueField v.valuationSubring) p := by
    dsimp only [p, F, v]
    infer_instance
  exact map_logOnePlusSeriesField_of_hasExtension v v p x hx

omit [CharZero L] in
private theorem sub_one_lt_one_of_integerPrincipalUnit {r : ℕ} (hr : 1 ≤ r)
    (a : principalUnits L r) :
    localIntegerValuation L ((((a : 𝒪[L]ˣ) : 𝒪[L]) : L) - 1) < 1 := by
  let b : fieldPrincipalUnits L 1 :=
    ⟨integerUnitsToFieldUnits L a, Subgroup.map_mono (principalUnits_antitone L hr)
      ⟨(a : 𝒪[L]ˣ), a.property, rfl⟩⟩
  let c := (localIntegerValuationPrincipalUnitsEquiv L 1).symm b
  have h := principalUnitSubOne_val_lt_one_ofWithZeroValuation (localIntegerValuation L) c
  unfold principalUnitSubOneOfWithZeroValuation at h
  dsimp only [c] at h
  rw [localIntegerValuationPrincipalUnitsEquiv_symm_apply_coe] at h
  exact h

theorem integerPrincipalUnitsLogEquiv_fieldVal (r : ℕ) (hr : localLogExpThreshold L < (r : ℚ))
    (a : principalUnits L r) :
    (((integerPrincipalUnitsLogEquiv L r hr (Additive.ofMul a) : 𝒪[L]) : L)) =
      logOnePlusSeriesFieldOfWithZeroValuation (localIntegerValuation L)
        ((((a : 𝒪[L]ˣ) : 𝒪[L]) : L) - 1)
        (fun j => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)) :=
  fieldPrincipalUnitsLogMulEquiv_fieldVal L r hr
    ((principalUnits L r).equivMapOfInjective (integerUnitsToFieldUnits L)
      (integerUnitsToFieldUnits_injective L) a)

/-- The deep logarithm commutes with the original integral Galois actions. -/
theorem integerPrincipalUnitsLogEquiv_galois (r : ℕ) (hr : localLogExpThreshold L < (r : ℚ))
    (σ : Gal(L/K)) (a : principalUnits L r) :
    (integerPrincipalUnitsLogEquiv L r hr
        (Additive.ofMul (galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure K L r σ a)) : 𝒪[L]) =
      galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ
        (integerPrincipalUnitsLogEquiv L r hr (Additive.ofMul a)) := by
  apply Subtype.ext
  rw [galoisGroupIntegerRingEquivOfIsIntegralClosure_apply,
    integerPrincipalUnitsLogEquiv_fieldVal, integerPrincipalUnitsLogEquiv_fieldVal]
  have hr₁ : 1 ≤ r := by
    have : (0 : ℚ) < (r : ℚ) := (localLogExpThreshold_pos L).trans hr
    exact_mod_cast this
  rw [logOnePlusSeriesField_galois K L σ _ (sub_one_lt_one_of_integerPrincipalUnit L hr₁ a),
    map_sub, map_one]
  rfl

end ClassFieldTheory.Brauer

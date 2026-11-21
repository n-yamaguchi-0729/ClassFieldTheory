/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.PowerResidueTameFormula
import Mathlib.Tactic.Ring

/-!
# The tame Hilbert formula for arbitrary field units

The existing geometric Hilbert symbol is evaluated by reducing the signed
valuation-zero unit `(-1)^(v(a)v(b)) * a^v(b) / b^v(a)`, where the positive
valuation is `v = -valuationMap`. The final formula contains no uniformizer
and retains the sign also when the exponent is even.
-/

@[expose] public section

noncomputable section

open scoped ValuativeRel

namespace LocalClassFieldTheory.Kummer

open KummerTheory LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

/-- The signed unit whose residue evaluates the geometric tame Hilbert symbol.
The positive valuation is the negative of the existing `valuationMap`. -/
noncomputable def tameHilbertUnit (a b : Kˣ) : 𝒪[K]ˣ :=
  integerUnitOfValuationMapZero K
    ((-1 : Kˣ) ^ ((-valuationMap K (Additive.ofMul a)) *
        (-valuationMap K (Additive.ofMul b))) *
      (a ^ (-valuationMap K (Additive.ofMul b)) /
        b ^ (-valuationMap K (Additive.ofMul a)))) (by
    have hneg : valuationMap K (Additive.ofMul (-1 : Kˣ)) = 0 := by
      change valuationMap K
        (Additive.ofMul (integerUnitsToFieldUnits K (-1))) = 0
      rw [valuationMap_apply]
      exact v_integerUnitsToFieldUnits K (-1)
    simp only [valuationMap_ofMul_mul, valuationMap_ofMul_zpow,
      valuationMap_ofMul_div, hneg, mul_zero, zero_add]
    ring)

/-- The valuation-ring unit is the literal signed expression in field units. -/
@[simp]
theorem integerUnitsToFieldUnits_tameHilbertUnit (a b : Kˣ) :
    integerUnitsToFieldUnits K (tameHilbertUnit K a b) =
      (-1 : Kˣ) ^ ((-valuationMap K (Additive.ofMul a)) *
        (-valuationMap K (Additive.ofMul b))) *
      (a ^ (-valuationMap K (Additive.ofMul b)) /
        b ^ (-valuationMap K (Additive.ofMul a))) :=
  integerUnitOfValuationMapZero_spec K _ _

/-- With an integral first unit, the signed unit specializes to the old
unit-first exponent, including its geometric sign. -/
theorem tameHilbertUnit_integerUnit (a : 𝒪[K]ˣ) (b : Kˣ) :
    tameHilbertUnit K (integerUnitsToFieldUnits K a) b =
      a ^ (-valuationMap K (Additive.ofMul b)) := by
  have ha : valuationMap K (Additive.ofMul (integerUnitsToFieldUnits K a)) = 0 := by
    rw [valuationMap_apply]
    exact v_integerUnitsToFieldUnits K a
  apply integerUnitsToFieldUnits_injective K
  rw [integerUnitsToFieldUnits_tameHilbertUnit, ha]
  simp only [neg_zero, zero_mul, zpow_zero, one_mul, div_one, map_zpow]

/-- The tame formula for the existing Hilbert symbol with both arguments
arbitrary units of the field. -/
theorem localHilbertSymbol_tame_formula_general
    (n : ℕ+)
    (hn : ValuativeRel.valuation K ((n : ℕ) : K) = 1)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    localHilbertSymbol K n (natCast_ne_zero_of_valuation_eq_one K n hn) hmu a b =
      localTamePowerResidueSymbol K n hn hmu (tameHilbertUnit K a b) := by
  let hnK := natCast_ne_zero_of_valuation_eq_one K n hn
  let piInv : Kˣ := inverseIntegerRingUniformizerFieldUnit K
  have hpi : valuationMap K (Additive.ofMul piInv) = 1 := by
    simpa only [piInv, valuationMap_apply] using
      v_inverseIntegerRingUniformizerFieldUnit K
  let r : ℤ := valuationMap K (Additive.ofMul a)
  let s : ℤ := valuationMap K (Additive.ofMul b)
  let ua : 𝒪[K]ˣ := uniformizerUnitFactor K piInv hpi a
  let ub : 𝒪[K]ˣ := uniformizerUnitFactor K piInv hpi b
  have ha : integerUnitsToFieldUnits K ua * piInv ^ r = a :=
    uniformizerUnitFactor_mul_uniformizer_zpow K piInv hpi a
  have hb : integerUnitsToFieldUnits K ub * piInv ^ s = b :=
    uniformizerUnitFactor_mul_uniformizer_zpow K piInv hpi b
  let B := fun x y : Kˣ => localHilbertSymbol K n hnK hmu x y
  let t : 𝒪[K]ˣ →* nthRootsSubgroup K (n : ℕ) :=
    (maximalLocalKummerPairingRightHom K n hnK hmu piInv).comp
      (integerUnitsToFieldUnits K)
  have ht_symbol (x : 𝒪[K]ˣ) : t x = B piInv (integerUnitsToFieldUnits K x) :=
    maximalLocalKummerPairingRightHom_eq_localHilbertSymbolHom
      K n hnK hmu piInv (integerUnitsToFieldUnits K x)
  have ht (x : 𝒪[K]ˣ) : t x = localTamePowerResidueSymbol K n hn hmu x :=
    (ht_symbol x).trans
      (localHilbertSymbol_inverseIntegerRingUniformizerFieldUnit_integerUnit_eq_tame
        K n hn hmu x)
  have hmul (x y z : Kˣ) : B (x * y) z = B x z * B y z :=
    map_mul (localHilbertSymbolHom K n hnK hmu z) x y
  have hzpow (x y : Kˣ) (m : ℤ) : B (x ^ m) y = B x y ^ m :=
    map_zpow (localHilbertSymbolHom K n hnK hmu y) x m
  have htneg : t (-1) * t (-1) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have htneginv : (t (-1))⁻¹ = t (-1) :=
    ((eq_inv_iff_mul_eq_one).2 htneg).symm
  have hdiag : B piInv piInv = t (-1) := by
    have h := localHilbertSymbol_neg_self K n hnK hmu piInv
    rw [show -piInv = (-1 : Kˣ) * piInv from (neg_one_mul piInv).symm,
      localHilbertSymbol_mul_right] at h
    have hneg : B piInv (-1) = t (-1) := (ht_symbol (-1)).symm
    change B piInv (-1) * B piInv piInv = 1 at h
    rw [hneg] at h
    have hdiagInv : B piInv piInv = (t (-1))⁻¹ :=
      (eq_inv_iff_mul_eq_one).2 ((mul_comm _ _).trans h)
    exact hdiagInv.trans htneginv
  have hpiB : B piInv b = t ub * t (-1) ^ s := by
    calc
      B piInv b = B piInv (integerUnitsToFieldUnits K ub * piInv ^ s) :=
        congrArg (B piInv) hb.symm
      _ = B piInv (integerUnitsToFieldUnits K ub) * B piInv (piInv ^ s) :=
        localHilbertSymbol_mul_right K n hnK hmu _ _ _
      _ = t ub * t (-1) ^ s := by
        have hpow : B piInv (piInv ^ s) = B piInv piInv ^ s :=
          localHilbertSymbol_zpow_right K n hnK hmu piInv piInv s
        exact congrArg₂ (· * ·) (ht_symbol ub).symm
          (hpow.trans (congrArg (· ^ s) hdiag))
  have hunit : ua ^ (-s) * (ub ^ r * (-1 : 𝒪[K]ˣ) ^ (s * r)) =
      tameHilbertUnit K a b := by
    have hratio : a ^ (-s) / b ^ (-r) =
        integerUnitsToFieldUnits K ub ^ r / integerUnitsToFieldUnits K ua ^ s := by
      calc
        a ^ (-s) / b ^ (-r) = b ^ r / a ^ s := by
          simp only [zpow_neg, div_eq_mul_inv, inv_inv]
          exact mul_comm _ _
        _ = (integerUnitsToFieldUnits K ub * piInv ^ s) ^ r /
            (integerUnitsToFieldUnits K ua * piInv ^ r) ^ s := by rw [ha, hb]
        _ = integerUnitsToFieldUnits K ub ^ r / integerUnitsToFieldUnits K ua ^ s := by
          rw [mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul,
            mul_comm s r, mul_div_mul_right_eq_div]
    apply integerUnitsToFieldUnits_injective K
    rw [integerUnitsToFieldUnits_tameHilbertUnit]
    change integerUnitsToFieldUnits K (ua ^ (-s) * (ub ^ r * (-1) ^ (s * r))) =
      (-1 : Kˣ) ^ ((-r) * (-s)) * (a ^ (-s) / b ^ (-r))
    have hneg : integerUnitsToFieldUnits K (-1) = (-1 : Kˣ) := by
      apply Units.ext
      rfl
    rw [hratio, neg_mul_neg]
    simp only [map_mul, map_zpow, hneg, zpow_neg, map_inv, div_eq_mul_inv]
    rw [mul_comm s r]
    ac_rfl
  change B a b = localTamePowerResidueSymbol K n hn hmu (tameHilbertUnit K a b)
  calc
    B a b = B (integerUnitsToFieldUnits K ua * piInv ^ r) b :=
      congrArg (fun x => B x b) ha.symm
    _ = B (integerUnitsToFieldUnits K ua) b * B piInv b ^ r := by rw [hmul, hzpow]
    _ = t ua ^ (-s) * (t ub * t (-1) ^ s) ^ r := by
      rw [hpiB]
      have hu := localHilbertSymbol_tame_formula K n hn hmu ua b
      change B (integerUnitsToFieldUnits K ua) b =
        localTamePowerResidueSymbol K n hn hmu ua ^ (-s) at hu
      rw [hu, ← ht]
    _ = t (ua ^ (-s) * (ub ^ r * (-1 : 𝒪[K]ˣ) ^ (s * r))) := by
      rw [map_mul, map_zpow, map_mul, map_zpow, map_zpow, mul_zpow, zpow_mul]
    _ = localTamePowerResidueSymbol K n hn hmu (tameHilbertUnit K a b) := by
      rw [hunit, ht]

/-- Reduction of the general tame formula is the literal `(q-1)/n` power
of the signed unit. The injective tame reduction of roots of unity therefore
also determines the original Hilbert-symbol value uniquely. -/
theorem localHilbertSymbol_tame_formula_general_reduction
    (n : ℕ+)
    (hn : ValuativeRel.valuation K ((n : ℕ) : K) = 1)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    (localNthRootsReduction K n
      (localHilbertSymbol K n (natCast_ne_zero_of_valuation_eq_one K n hn) hmu a b)).1 =
      residueUnitsConcreteEquiv K
        (integerUnitsToResidueUnits K (tameHilbertUnit K a b)) ^
          ((Nat.card 𝓀[K] - 1) / (n : ℕ)) := by
  rw [localHilbertSymbol_tame_formula_general K n hn hmu a b]
  let : Fintype 𝓀[K] := Fintype.ofFinite _
  have h := congrArg Subtype.val
    (localNthRootsReductionEquiv_localTamePowerResidueSymbol
      K n hn hmu (tameHilbertUnit K a b))
  change (localNthRootsReduction K n
      (localTamePowerResidueSymbol K n hn hmu (tameHilbertUnit K a b))).1 =
    residueUnitsConcreteEquiv K
      (integerUnitsToResidueUnits K (tameHilbertUnit K a b)) ^
        ((Fintype.card 𝓀[K] - 1) / (n : ℕ)) at h
  rw [Nat.card_eq_fintype_card]
  exact h

end LocalClassFieldTheory.Kummer

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PowerClassFiniteness
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitPowerIndexFormulas
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Power indices in a local field of positive characteristic

The intrinsic local-field valuation supplies the complete discrete valuation
used by the established unit-structure formula. Its characteristic, the
coprimality condition, and the finite principal-unit quotient are obtained
from the field and the actual nonzero exponent.
-/

noncomputable section

namespace LocalFieldTheory

open scoped ValuativeRel
open LocalFieldTheory.DiscreteValuationField

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

/-- In positive characteristic the power index is n times the number of n-th
roots of unity. No finiteness or principal-unit structure is assumed separately. -/
theorem card_nthPowerQuotient_of_positiveCharacteristic
    (p : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ) (hnK : (n : K) ≠ 0) :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * Nat.card (rootsOfUnity n K) := by
  have hn : n ≠ 0 := by
    intro h
    exact hnK (by rw [h, Nat.cast_zero])
  have : NeZero n := ⟨hn⟩
  let v := localIntegerValuation K
  let F : LocalField K := LocalField.ofWithZeroValuation v
  have hres : F.residueCharacteristic = p :=
    F.residueCharacteristic_eq_of_charP p (Fact.out : p.Prime).ne_zero
  have hchar : CharP K F.residueCharacteristic := by
    rw [hres]
    infer_instance
  have hpn : ¬ F.residueCharacteristic ∣ n := by
    intro hdiv
    exact hnK ((CharP.cast_eq_zero_iff K F.residueCharacteristic n).mpr hdiv)
  have hcoprime : Fact (Nat.Coprime n F.residueCharacteristic) :=
    ⟨(F.residueCharacteristic_prime.coprime_iff_not_dvd.mpr hpn).symm⟩
  let valuedK : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let e := LocalField.chosenFirstPrincipalUnitStructure_equalCharacteristic v
  let U1 := CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1
  let A := ℕ → ℤ_[F.residueCharacteristic]
  have hA : Finite (A ⧸ nsmulAddSubgroup A n) := inferInstance
  let emul : U1 ≃* Multiplicative A := by
    let : TopologicalSpace K := valuedK.toTopologicalSpace
    exact e.symm.toMulEquiv
  have hU : Finite (U1 ⧸ (powMonoidHom n : U1 →* U1).range) :=
    finite_nthPowerQuotient_of_mulEquiv U1 (Multiplicative A) n emul
  have hK : Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) :=
    finite_nthPowerQuotient_of_natCast_ne_zero K n hnK
  simpa only [powMonoidHom_ker_units_eq_rootsOfUnity] using
    (LocalField.equal_fieldIndex v (n := n))

/-- A positive-characteristic local field containing the n-th roots of unity
has exactly n squared power classes, for n prime to the characteristic. -/
theorem card_nthPowerQuotient_eq_sq_of_positiveCharacteristic
    (p : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Nat.card (Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) = (n : ℕ) ^ 2 := by
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := hmu
  rw [card_nthPowerQuotient_of_positiveCharacteristic K p n hnK,
    (isPrimitiveRoot_of_mem_primitiveRoots hζ).card_rootsOfUnity, pow_two]

end LocalFieldTheory

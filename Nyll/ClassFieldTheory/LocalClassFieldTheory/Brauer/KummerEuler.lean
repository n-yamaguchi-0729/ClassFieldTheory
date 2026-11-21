/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.KummerTrace
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PowerClassFiniteness
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitPowerIndexFormulas

/-! # Low-degree cardinalities for the actual local Kummer coefficient -/

@[expose] public section

open scoped ValuativeRel
open TopRep LocalFieldTheory LocalFieldTheory.DiscreteValuationField

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

local notation "Mu" => separableMuTopRep K
local notation "H" => _root_.continuousCohomology

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem card_localKummerH0 (n : ℕ) :
    Nat.card (H 0 (Mu n)) = Nat.card ((powMonoidHom n : Kˣ →* Kˣ).ker) :=
  Nat.card_congr (separableMuH0EquivBaseRoots K n).toEquiv

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem card_localKummerH1 (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0) :
    Nat.card (H 1 (Mu n)) = Nat.card (Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) :=
  Nat.card_congr (separableMuH1EquivPowerClasses K n hn).symm.toEquiv

theorem card_localKummerH2 (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0) :
    Nat.card (H 2 (Mu n)) = (n : ℕ) :=
  (Nat.card_congr (localKummerTrace K n hn).toEquiv).trans (Nat.card_zmod _)

/-- The original local Kummer cohomology is finite in degrees zero, one, and two. -/
theorem finite_localKummerH012 (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0) :
    Finite (H 0 (Mu n)) ∧ Finite (H 1 (Mu n)) ∧ Finite (H 2 (Mu n)) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let : Finite (Additive ((powMonoidHom (n : ℕ) : Kˣ →* Kˣ).ker)) :=
    inferInstanceAs (Finite (rootsOfUnity (n : ℕ) K))
  let : Finite (Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) :=
    finite_nthPowerQuotient_of_natCast_ne_zero K n hn
  exact ⟨Finite.of_equiv _ (separableMuH0EquivBaseRoots K n).symm.toEquiv,
    Finite.of_equiv _ (separableMuH1EquivPowerClasses K n hn).toEquiv,
    Finite.of_equiv _ (localKummerTrace K n hn).symm.toEquiv⟩

open LocalField (chosenMixed_firstPrincipalUnitStructure_ofWithZeroValuation) in
/-- The low-degree Kummer Euler product in mixed characteristic includes the
usual p-adic factor from the dimension of the principal-unit free part. -/
theorem localKummerEuler_mixed [CharZero K] (n : ℕ+) :
    let v := localIntegerValuation K
    let F := LocalField.ofWithZeroValuation v
    let : LocalField.MixedWithZeroValuationContext v := LocalField.mixedWithZeroValuationContext v
    let d := Module.finrank ℚ_[F.residueCharacteristic] K
    Nat.card (H 1 (Mu n)) =
      Nat.card (H 2 (Mu n)) * (Nat.card (H 0 (Mu n)) *
        F.residueCharacteristic ^ (d * padicValNat F.residueCharacteristic n)) := by
  intro v F ctx d
  have hn : ((n : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let : Finite (Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) :=
    finite_nthPowerQuotient_of_natCast_ne_zero K n hn
  obtain ⟨a, e⟩ := chosenMixed_firstPrincipalUnitStructure_ofWithZeroValuation
    v (localIntegerValuation_surjective K)
  let U := CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1
  let T := ZMod (F.residueCharacteristic ^ a)
  let A := T × (Fin d → ℤ_[F.residueCharacteristic])
  let : NeZero (F.residueCharacteristic ^ a) :=
    ⟨pow_ne_zero _ F.residueCharacteristic_prime.ne_zero⟩
  let : Finite (A ⧸ nsmulAddSubgroup A (n : ℕ)) := by infer_instance
  let m : U ≃* Multiplicative A := by
    let valued : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    let : TopologicalSpace K := valued.toTopologicalSpace
    exact e.symm.toMulEquiv
  let : Finite (U ⧸ (powMonoidHom (n : ℕ) : U →* U).range) :=
    finite_nthPowerQuotient_of_mulEquiv U (Multiplicative A) n m
  rw [card_localKummerH1 K n hn, card_localKummerH2 K n hn, card_localKummerH0]
  exact LocalField.mixed_fieldIndex v (localIntegerValuation_surjective K) (n := (n : ℕ))

open LocalField (chosenFirstPrincipalUnitStructure_equalCharacteristic) in
/-- For an invertible exponent in equal characteristic, the local Kummer
Euler product is one. -/
theorem localKummerEuler_equal (p : ℕ) [Fact p.Prime] [CharP K p]
    (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0) :
    Nat.card (H 1 (Mu n)) = Nat.card (H 2 (Mu n)) * Nat.card (H 0 (Mu n)) := by
  let v := localIntegerValuation K
  let F := LocalField.ofWithZeroValuation v
  have hp : F.residueCharacteristic = p :=
    F.residueCharacteristic_eq_of_charP p (Fact.out : p.Prime).ne_zero
  let : CharP K F.residueCharacteristic := by
    rw [hp]
    infer_instance
  have hpn : ¬ F.residueCharacteristic ∣ (n : ℕ) :=
    fun h => hn ((CharP.cast_eq_zero_iff K F.residueCharacteristic (n : ℕ)).mpr h)
  let : Fact (Nat.Coprime (n : ℕ) F.residueCharacteristic) :=
    ⟨(F.residueCharacteristic_prime.coprime_iff_not_dvd.mpr hpn).symm⟩
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let : Finite (Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) :=
    finite_nthPowerQuotient_of_natCast_ne_zero K n hn
  let e := chosenFirstPrincipalUnitStructure_equalCharacteristic v
  let U := CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF 1
  let A := ℕ → ℤ_[F.residueCharacteristic]
  let : Finite (A ⧸ nsmulAddSubgroup A (n : ℕ)) := by infer_instance
  let m : U ≃* Multiplicative A := by
    let valued : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    let : TopologicalSpace K := valued.toTopologicalSpace
    exact e.symm.toMulEquiv
  let : Finite (U ⧸ (powMonoidHom (n : ℕ) : U →* U).range) :=
    finite_nthPowerQuotient_of_mulEquiv U (Multiplicative A) n m
  rw [card_localKummerH1 K n hn, card_localKummerH2 K n hn, card_localKummerH0]
  exact LocalField.equal_fieldIndex v (n := (n : ℕ))

/-- Degree two has a nonzero class for every invertible exponent greater than one. -/
theorem exists_localKummerH2_ne_zero (n : ℕ+) (hn : ((n : ℕ) : K) ≠ 0) (hn₁ : 1 < (n : ℕ)) :
    ∃ x : H 2 (Mu n), x ≠ 0 := by
  let : Fact (1 < (n : ℕ)) := ⟨hn₁⟩
  let e := localKummerTrace K n hn
  refine ⟨e.symm 1, fun hx => ?_⟩
  have h := congrArg e hx
  rw [e.apply_symm_apply, map_zero] at h
  exact one_ne_zero h

end ClassFieldTheory.Brauer

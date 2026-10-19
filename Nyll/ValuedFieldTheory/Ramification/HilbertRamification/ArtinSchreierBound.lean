/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ArtinSchreier.FiniteExtension
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.DVRRamificationOrder
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness
import Nyll.ValuedFieldTheory.Ramification.Herbrand.Bounds
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.AddVal
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# A ramification bound for Artin–Schreier extensions

For a parameter with pole order at most p n, multiplying its root by the
n-th power of a base uniformizer gives an integral element. A nonidentity
Galois automorphism displaces this element by that same uniformizer power
times a nonzero prime-field constant. The fundamental degree identity
therefore makes the lower group at p n trivial. This bound suffices for
moduli whose coefficients are divisible by p, without a reduced parameter.
-/

noncomputable section

namespace RamificationTheory.HilbertRamification.Higher

open Polynomial ArtinSchreierTheory
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- A pole bound divisible by the characteristic kills the corresponding
actual lower ramification group of an Artin–Schreier extension. -/
theorem lowerRamificationGroup_artinSchreier_eq_bot
    (base : CompleteDVF.{0, 0} K) (target : CompleteDVF.{0, 0} L)
    [base.valuation.HasExtension target.valuation]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : base.valuationSubring) (hπ : Irreducible π) (n : ℕ)
    (a : K) (ha : (π : K) ^ (p * n) * a ∈ base.valuation.valuationSubring)
    (β : L) (hβ : β ^ p - β = algebraMap K L a)
    (hgen : Algebra.adjoin K {β} = ⊤) :
    lowerRamificationGroup (base := base.toDVF) (target := target.toDVF)
      (hasUniqueValuationExtension_of_finite_separable base target) (p * n : ℕ) = ⊥ := by
  let A := base.valuationSubring
  let B := target.valuationSubring
  have hABL : IsScalarTower A B L :=
    Valuation.valuationSubring_isScalarTower_of_hasExtension base.valuation target.valuation
  have hAKL : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hIC : IsIntegralClosure B A L :=
    target_valuationSubring_isIntegralClosure_of_finite_separable base target
  have hfinite : Module.Finite A B := IsIntegralClosure.finite A K L B
  have hcharL : CharP L p := (Algebra.charP_iff K L p).mp inferInstance
  have hcharB : CharP B p := CharP.subring L p target.valuation.valuationSubring.toSubring
  let πB : B := algebraMap A B π
  have hmapπ : algebraMap B L πB = algebraMap K L (π : K) := by
    exact IsScalarTower.algebraMap_apply A B L π
  have hπB0 : πB ≠ 0 := by
    intro h
    apply hπ.ne_zero
    apply Subtype.ext
    apply (algebraMap K L).injective
    rw [← hmapπ, h, map_zero]
    exact (map_zero (algebraMap K L)).symm
  let e : ℕ := (IsDiscreteValuationRing.addVal B πB).toNat
  have hπval : IsDiscreteValuationRing.addVal B πB ≠ ⊤ :=
    (IsDiscreteValuationRing.addVal_eq_top_iff).not.mpr hπB0
  have he : e ≤ p := by
    have hinj : Function.Injective (algebraMap A B) := by
      intro x y h
      apply Subtype.ext
      apply (algebraMap K L).injective
      exact congrArg (algebraMap B L) h
    have heram : Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal = e :=
      DiscreteValuationRing.ramificationIdx'_eq_addVal_uniformizer A B hinj π hπ
    have hfund := ideal_ramificationIdx_mul_inertiaDeg_eq_finrank_of_finite_separable
      (K := K) (L := L) base target
    rw [heram] at hfund
    have hf : 0 < target.maximalIdeal.inertiaDeg A := by
      have hLie : target.maximalIdeal.LiesOver base.maximalIdeal :=
        maximalIdeal_liesOver base target
      exact target.maximalIdeal.inertiaDeg_pos A
    have hdegree : Module.finrank K L ≤ p :=
      Nat.le_of_dvd (Fact.out : p.Prime).pos
        (finrank_dvd_prime_of_adjoin_eq_top p a β hβ hgen)
    exact (Nat.le_mul_of_pos_right e hf).trans (hfund.le.trans hdegree)
  let a₀ : A := ⟨(π : K) ^ (p * n) * a, ha⟩
  let P : A[X] := X ^ p - (C (π ^ (n * (p - 1))) * X + C a₀)
  have hPmonic : P.Monic := by
    apply monic_X_pow_sub
    exact (degree_linear_le).trans_lt
      (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hPβ : aeval ((algebraMap K L (π : K)) ^ n * β) P = 0 := by
    simp only [P, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C]
    change ((algebraMap K L (π : K)) ^ n * β) ^ p -
      ((algebraMap K L (π : K)) ^ (n * (p - 1)) *
        ((algebraMap K L (π : K)) ^ n * β) +
        algebraMap K L ((π : K) ^ (p * n) * a)) = 0
    have hexp : n * (p - 1) + n = p * n := by
      calc
        n * (p - 1) + n = n * ((p - 1) + 1) := by ring
        _ = p * n := by rw [Nat.sub_add_cancel (Fact.out : p.Prime).one_le, Nat.mul_comm]
    rw [mul_pow, ← pow_mul, Nat.mul_comm n p, map_mul, map_pow,
      ← mul_assoc, ← pow_add, hexp]
    calc
      (algebraMap K L (π : K)) ^ (p * n) * β ^ p -
          ((algebraMap K L (π : K)) ^ (p * n) * β +
            (algebraMap K L (π : K)) ^ (p * n) * algebraMap K L a) =
          (algebraMap K L (π : K)) ^ (p * n) * (β ^ p - β - algebraMap K L a) := by ring
      _ = 0 := by rw [hβ, sub_self, mul_zero]
  obtain ⟨γ, hγ⟩ := (IsIntegralClosure.isIntegral_iff (A := B) (R := A)).mp
    (show IsIntegral A ((algebraMap K L (π : K)) ^ n * β) from ⟨P, hPmonic, hPβ⟩)
  apply eq_bot_iff.mpr
  intro σ hσ
  change σ = 1
  by_contra hσ1
  let χ := rootCharacter p L a β hβ
  have hχ : χ σ ≠ 1 := fun h => hσ1
    (rootCharacter_injective_of_adjoin_eq_top p a β hβ hgen (h.trans χ.map_one.symm))
  let c : B := (ZMod.castHom (dvd_refl p) B) (χ σ).toAdd
  have hz0 : (χ σ).toAdd ≠ 0 := hχ
  have hcunit : IsUnit c :=
    (isUnit_iff_ne_zero.mpr hz0).map (ZMod.castHom (dvd_refl p) B)
  have hc : algebraMap B L c = σ β - β := by
    dsimp only [c]
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, map_natCast]
    simpa only [ZMod.castHom_apply, ZMod.cast_eq_val] using rootCharacter_cast p L a β hβ σ
  have hdispl : valuationSubringAutOfUniqueExtension
      (base := base.toDVF) (target := target.toDVF)
      (hasUniqueValuationExtension_of_finite_separable base target) σ γ - γ = πB ^ n * c := by
    apply Subtype.ext
    change σ (algebraMap B L γ) - algebraMap B L γ = algebraMap B L (πB ^ n * c)
    rw [hγ, map_mul, map_pow, σ.commutes, map_mul, map_pow, hmapπ, hc]
    ring
  have hmem : (p * n + 1 : ℕ∞) ≤ IsDiscreteValuationRing.addVal B
      (valuationSubringAutOfUniqueExtension
        (base := base.toDVF) (target := target.toDVF)
        (hasUniqueValuationExtension_of_finite_separable base target) σ γ - γ) := by
    apply (IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_addVal_ge _ (p * n + 1)).mp
    exact (realRamificationIdeal_nat (target := target.toDVF) (p * n)) ▸ hσ γ
  rw [hdispl, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hcunit, add_zero,
    ← ENat.natCast_toNat hπval, nsmul_eq_mul] at hmem
  have hbad : p * n + 1 ≤ n * e := by exact_mod_cast hmem
  have hbound : n * e ≤ p * n := (Nat.mul_le_mul_left n he).trans_eq (Nat.mul_comm n p)
  omega

/-- At a characteristic-divisible pole bound, the actual upper ramification
group is also trivial. -/
theorem upperRamificationGroup_artinSchreier_eq_bot
    (base : CompleteDVF.{0, 0} K) (target : CompleteDVF.{0, 0} L)
    [base.valuation.HasExtension target.valuation]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : base.valuationSubring) (hπ : Irreducible π) (n : ℕ)
    (a : K) (ha : (π : K) ^ (p * n) * a ∈ base.valuation.valuationSubring)
    (β : L) (hβ : β ^ p - β = algebraMap K L a)
    (hgen : Algebra.adjoin K {β} = ⊤) :
    upperRamificationGroupOfUniqueExtension
      (base := base.toDVF) (target := target.toDVF)
      (hasUniqueValuationExtension_of_finite_separable base target) (p * n : ℕ) = ⊥ := by
  let huniq : DiscreteValuationField.DVF.HasUniqueValuationExtension.{0, 0, 0, 0, 0}
      base.toDVF target.toDVF :=
    hasUniqueValuationExtension_of_finite_separable base target
  have hφ : herbrandFunctionOfUniqueExtension
      (base := base.toDVF) (target := target.toDVF) huniq (p * n : ℕ) ≤ (p * n : ℕ) :=
    DiscreteValuationField.AntitoneNormalSubgroupFiltration.herbrandFunction_nat_le
      (lowerRamificationFiltrationOfUniqueExtension
        (base := base.toDVF) (target := target.toDVF) huniq) (p * n)
  have hψ : (p * n : ℕ) ≤ inverseHerbrandFunctionOfUniqueExtension
      (base := base.toDVF) (target := target.toDVF) huniq (p * n : ℕ) := by
    calc
      (p * n : ℕ) = inverseHerbrandFunctionOfUniqueExtension
          (base := base.toDVF) (target := target.toDVF) huniq
          (herbrandFunctionOfUniqueExtension
            (base := base.toDVF) (target := target.toDVF) huniq (p * n : ℕ)) :=
        (inverseHerbrandFunctionOfUniqueExtension_eta
          (base := base.toDVF) (target := target.toDVF) huniq (p * n : ℕ)).symm
      _ ≤ inverseHerbrandFunctionOfUniqueExtension
          (base := base.toDVF) (target := target.toDVF) huniq (p * n : ℕ) :=
        (inverseHerbrandFunctionOfUniqueExtension_strictMono
          (base := base.toDVF) (target := target.toDVF) huniq).monotone hφ
  apply eq_bot_iff.mpr
  exact (lowerRamificationGroup_antitone
    (base := base.toDVF) (target := target.toDVF) huniq hψ).trans
      (lowerRamificationGroup_artinSchreier_eq_bot base target p π hπ n a ha β hβ hgen).le

end RamificationTheory.HilbertRamification.Higher

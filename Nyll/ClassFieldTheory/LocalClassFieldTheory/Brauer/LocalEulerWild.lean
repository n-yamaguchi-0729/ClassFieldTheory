/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalEulerPrimeCoefficient
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalWildH1
public import Nyll.ValuedFieldTheory.Valuation.Henselian.RootsOfUnity

/-! # Local Euler characteristic for modules with zero wild invariants -/

@[expose] public section

open CategoryTheory ContinuousCohomology TopRep LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open RamificationTheory.HilbertRamification.ValuationSubring
open scoped BigOperators ValuativeRel

noncomputable section

namespace ClassFieldTheory.Brauer

attribute [local instance] separableAbsoluteGalois_locallyCompact

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K]

local notation "Ω" => SeparableClosure K
local notation "G" => Gal(Ω/K)
local notation "H" => continuousCohomology

omit [CharZero K] in
/-- Normalizing the value group preserves the residue characteristic. -/
theorem localIntegerResidueCharacteristic_eq :
    (LocalField.ofWithZeroValuation (localIntegerValuation K)).residueCharacteristic =
      ringChar 𝓀[K] := by
  let e := IsLocalRing.ResidueField.mapEquiv (localIntegerValuationSubringEquiv K)
  let : CharP (IsLocalRing.ResidueField (localIntegerValuation K).valuationSubring)
      (ringChar 𝓀[K]) := charP_of_injective_ringHom e.symm.injective _
  change ringChar (IsLocalRing.ResidueField (localIntegerValuation K).valuationSubring) =
    ringChar 𝓀[K]
  exact ringChar.eq _ _

/-- The normalized order has weight one on finite prime-annihilated
coefficients away from the residue characteristic. -/
theorem localCoefficientOrderNorm_prime_awayResidue (p : ℕ) [Fact p.Prime]
    (hpq : p ≠ ringChar 𝓀[K]) (A : Type*) [AddCommGroup A] [Finite A]
    (hpA : ∀ a : A, p • a = 0) : localCoefficientOrderNorm K (Nat.card A) = 1 := by
  let moduleA : Module (ZMod p) A := AddCommGroup.zmodModule hpA
  let : Module (ZMod p) A := moduleA
  let finiteA : Module.Finite (ZMod p) A := Module.Finite.of_finite
  let F := LocalField.ofWithZeroValuation (localIntegerValuation K)
  have hq : F.residueCharacteristic ≠ p := by
    change (LocalField.ofWithZeroValuation (localIntegerValuation K)).residueCharacteristic ≠ p
    rw [localIntegerResidueCharacteristic_eq]
    exact hpq.symm
  have hcard := @Module.natCard_eq_pow_finrank (ZMod p) A _ _ moduleA finiteA
  rw [Nat.card_zmod] at hcard
  rw [hcard]
  let : Fact F.residueCharacteristic.Prime := ⟨F.residueCharacteristic_prime⟩
  have hv : multiplicity
      (LocalField.ofWithZeroValuation (localIntegerValuation K)).residueCharacteristic p = 0 :=
    multiplicity_primes hq
  unfold localCoefficientOrderNorm
  dsimp only
  simp only [Nat.padicValNat_def, Nat.multiplicity_pow, hv, mul_zero, pow_zero]

variable (W : ValuationSubring (SeparableClosure K)) (p : ℕ) [Fact p.Prime]

local notation "Mu" => separableMuTopRep K p
local notation "N" => ramificationGroupInAut K W

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K] in
/-- Wild inertia fixes the original roots of unity when their order is
invertible in the upper residue field. -/
theorem localWild_mu_fixed (hpW : (p : IsLocalRing.ResidueField W) ≠ 0)
    (σ : N) (x : Mu) : (Mu).ρ σ.val x = x := by
  let : NeZero (p : IsLocalRing.ResidueField W) := ⟨hpW⟩
  have hσ := ramificationGroupInAut_le_inertiaGroupInAut (K := K) W σ.property
  obtain ⟨τ, hτ, hτval⟩ := hσ
  let z : Ω := x.val.toMul.val
  have hz : z ^ p = 1 := by
    exact congrArg (fun y : Mu => y.val.toMul.val) (separableMuTopRep_nsmul_eq_zero K p x)
  have hval : W.valuation z = 1 :=
    (pow_eq_one_iff_of_nonneg zero_le (Fact.out : p.Prime).ne_zero).mp (by
      rw [← map_pow, hz, map_one])
  let a : W := ⟨z, W.mem_of_valuation_le_one z hval.le⟩
  let ξ : rootsOfUnity p W := rootsOfUnity.mkOfPowEq a (Subtype.ext hz)
  let e : W ≃+* W := MulSemiringAction.toRingEquiv (decompositionGroup K W) W τ
  have hres : restrictRootsOfUnity (IsLocalRing.residue W) p
      (restrictRootsOfUnity e.toRingHom p ξ) =
        restrictRootsOfUnity (IsLocalRing.residue W) p ξ := by
    apply rootsOfUnity.coe_injective
    change IsLocalRing.residue W (e a) = IsLocalRing.residue W a
    have he : residueAction K W τ = 1 := hτ
    calc
      _ = τ • IsLocalRing.residue W a := by rw [← IsLocalRing.ResidueField.residue_smul]; rfl
      _ = _ := DFunLike.congr_fun he (IsLocalRing.residue W a)
  have heq := W.rootsOfUnityReduction_injective p hres
  apply Subtype.ext
  apply Units.ext
  change σ.val z = z
  rw [← hτval]
  exact congrArg (fun t : rootsOfUnity p W => (((t : Wˣ) : W) : Ω)) heq

variable (A : TopRep.{u} ℤ Gal(SeparableClosure K/K)) [Finite A] [DiscreteTopology A]

local notation "D" => discreteLinearDual A Mu

private def restrictedCoefficientPerm : N →* Equiv.Perm A where
  toFun g :=
    { toFun := A.ρ g.val
      invFun := A.ρ g.val⁻¹
      left_inv := fun x => by
        have h := DFunLike.congr_fun (map_mul A.ρ g.val⁻¹ g.val) x
        rw [inv_mul_cancel, map_one] at h
        exact h.symm
      right_inv := fun x => by
        have h := DFunLike.congr_fun (map_mul A.ρ g.val g.val⁻¹) x
        rw [mul_inv_cancel, map_one] at h
        exact h.symm }
  map_one' := Equiv.ext fun x => DFunLike.congr_fun (map_one A.ρ) x
  map_mul' g h := Equiv.ext fun x => DFunLike.congr_fun (map_mul A.ρ g.val h.val) x

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K] in
private theorem restrictedCoefficientPerm_locallyConstant
    (hA : Continuous (fun ga : G × A => A.ρ ga.1 ga.2)) :
    IsLocallyConstant (restrictedCoefficientPerm K W A) := by
  have hc : Continuous (fun g : N => fun x : A => A.ρ g.val x) := by
    apply continuous_pi
    intro x
    exact hA.comp (continuous_subtype_val.prodMk continuous_const)
  have hl := (IsLocallyConstant.iff_continuous _).mpr hc
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro g
  obtain ⟨U, hU, hg, hconst⟩ := hl.exists_open g
  exact ⟨U, hU, hg, fun x hx => Equiv.ext (congrFun (hconst x hx))⟩

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K] in
private theorem localWild_dual_fixed_eq_zero (q : ℕ) [Fact q.Prime]
    [CharP (IsLocalRing.ResidueField W) q] (hpq : p ≠ q)
    (hA : Continuous (fun ga : G × A => A.ρ ga.1 ga.2))
    (hfix : ∀ a : A, (∀ g : N, A.ρ g.val a = a) → a = 0)
    (f : D) (hf : ∀ g : N, (D).ρ g.val f = f) : f = 0 := by
  let α := restrictedCoefficientPerm K W A
  let Q := α.range
  let : Fintype Q := Fintype.ofFinite Q
  let : Module ℤ A := A.hV2
  let : Module ℤ Mu := (Mu).hV2
  let F := discreteLinearDualMap A Mu f
  let s (x : A) : A := ∑ g : Q, g.val x
  have hsum (g : N) (x : A) : A.ρ g.val (s x) = s x := by
    let γ : Q := ⟨α g, ⟨g, rfl⟩⟩
    unfold s
    rw [map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft γ) _ _ (fun _ => rfl)
  have hs (x : A) : s x = 0 := hfix _ (fun g => hsum g x)
  have hpW : (p : IsLocalRing.ResidueField W) ≠ 0 := fun h =>
    hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) (Fact.out : p.Prime)).mp
      ((CharP.cast_eq_zero_iff _ q p).mp h)).symm
  have hF (g : Q) (x : A) : F (g.val x) = F x := by
    obtain ⟨τ, hτ⟩ := g.property
    rw [← hτ]
    have he := discreteLinearDualEvaluation_equivariant A Mu τ.val x f
    rw [hf τ, localWild_mu_fixed K W p hpW τ] at he
    exact he
  obtain ⟨j, hj⟩ := (localWild_locallyConstant_range_isPGroup K W q α
    (restrictedCoefficientPerm_locallyConstant K W A hA)).exists_card_eq
  have hcard : ¬ p ∣ Fintype.card Q := by
    rw [← Nat.card_eq_fintype_card, hj]
    exact fun hd => hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : q.Prime)).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow hd))
  let : Module (ZMod p) Mu := AddCommGroup.zmodModule (separableMuTopRep_nsmul_eq_zero K p)
  have hc : (Fintype.card Q : ZMod p) ≠ 0 := fun h => hcard ((CharP.cast_eq_zero_iff _ p _).mp h)
  suffices h : F = (0 : A →ₗ[ℤ] Mu) by exact h
  apply LinearMap.ext
  intro x
  change F x = 0
  have hsumF : Fintype.card Q • F x = 0 := by
    calc
      _ = ∑ g : Q, F x := by rw [Finset.sum_const, Finset.card_univ]
      _ = ∑ g : Q, F (g.val x) := Finset.sum_congr rfl (fun g _ => (hF g x).symm)
      _ = F (s x) := (map_sum F _ _).symm
      _ = 0 := by rw [hs, map_zero]
  let c : ZMod p := Fintype.card Q
  have hcz : c • F x = 0 := (Nat.cast_smul_eq_nsmul (ZMod p) (Fintype.card Q) (F x)).trans hsumF
  calc
    F x = (c⁻¹ * c) • F x := by rw [inv_mul_cancel₀ hc, one_smul]
    _ = c⁻¹ • (c • F x) := mul_smul _ _ _
    _ = 0 := by rw [hcz, smul_zero]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]
    [Finite A] [DiscreteTopology A] in
private theorem localH0_eq_zero_of_restriction
    (hfix : ∀ a : A, (∀ g : N, A.ρ g.val a = a) → a = 0)
    (x : H 0 A) : x = 0 := by
  apply (ConcreteCategory.bijective_of_isIso (zeroIso A).hom).injective
  rw [map_zero]
  apply Subtype.ext
  exact hfix _ (fun g => ((zeroIso A).hom x).property g.val)

/-- With zero wild invariants away from the residue prime, all three local
cohomology groups vanish and the normalized coefficient weight is one. -/
theorem localEulerCoefficient_wild_noInvariants (V : ValuationSubring K)
    [HenselianRing V (IsLocalRing.maximalIdeal V)] [V.valuation.HasExtension W.valuation]
    [CharP (IsLocalRing.ResidueField W) (ringChar 𝓀[K])] (hpq : p ≠ ringChar 𝓀[K])
    (hpA : ∀ a : A, p • a = 0) (hA : Continuous (fun ga : G × A => A.ρ ga.1 ga.2))
    (hfix : ∀ a : A, (∀ g : N, A.ρ g.val a = a) → a = 0) :
    hasLowDegreeEulerCharacteristic G (localCoefficientOrderNorm K) A := by
  let q := ringChar 𝓀[K]
  let : Fact q.Prime := ⟨CharP.prime_ringChar 𝓀[K]⟩
  let n : ℕ+ := ⟨p, (Fact.out : p.Prime).pos⟩
  have hn : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hz (i : ℕ) (hi : i < 3) (x : H i A) : x = 0 := by
    interval_cases i
    · exact localH0_eq_zero_of_restriction K W A hfix x
    · exact localH1_eq_zero_of_wild_noInvariants K V W p q hpq A hpA hA hfix x
    · have hd := (localTatePairingAdjoints_bijective K n A hn hA hpA).2.2.injective
      apply hd
      rw [map_zero]
      apply AddMonoidHom.ext
      intro y
      have hy := localH0_eq_zero_of_restriction K W D
        (localWild_dual_fixed_eq_zero K W p A q hpq hA hfix) y
      rw [hy]
      exact map_zero (localTatePairingTwoAdjoint K n A hn x)
  let C := (continuousModuleComplexFunctor G).obj A
  have hf (i : ℕ) (hi : i < 3) : Subsingleton (C.homology i) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (continuousModuleComplex_isZero_of_cohomology_eq_zero G A i (hz i hi))
  have hc (i : ℕ) (hi : i < 3) : Nat.card (C.homology i) = 1 := by
    let : Subsingleton (C.homology i) := hf i hi
    exact Nat.card_unique
  refine ⟨fun i hi => ?_, ?_⟩
  · let : Subsingleton (C.homology i) := hf i hi
    infer_instance
  change lowDegreeEulerCharacteristic C = localCoefficientOrderNorm K (Nat.card A)
  rw [localCoefficientOrderNorm_prime_awayResidue K p hpq A hpA]
  simp only [lowDegreeEulerCharacteristic, hc 0 (by decide), hc 1 (by decide), hc 2 (by decide),
    Nat.cast_one, mul_one, div_one]

end ClassFieldTheory.Brauer

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.ContinuousUnramified
public import Nyll.GaloisCohomology.Kummer.LiftedCyclicUnitsH2BaseChange
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation

/-! # Restriction of finite unramified Brauer invariants -/

@[expose] public section

open scoped ValuativeRel
open ClassFieldTower.Cohomology ContinuousCohomology LocalClassFieldTheory LocalFieldTheory
  LocalFieldTheory.IsNonarchimedeanLocalField Module

noncomputable section

namespace ClassFieldTheory.Brauer

universe u v w

section Ordinary

variable (K : Type u) (E : Type v) (M N : Type w)
    [Field K] [Field E] [Field M] [Field N]
    [Algebra K E] [Algebra K M] [Algebra K N] [Algebra E N] [Algebra M N]
    [IsScalarTower K E N] [IsScalarTower K M N]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel M] [UniformSpace M] [IsUniformAddGroup M] [IsNonarchimedeanLocalField M]
    [ValuativeRel N] [UniformSpace N] [IsUniformAddGroup N] [IsNonarchimedeanLocalField N]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    [FiniteDimensional K M] [IsGalois K M]
    [FiniteDimensional E N] [IsGalois E N]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E)]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation M)]
    [Valuation.HasExtension (ValuativeRel.valuation E) (ValuativeRel.valuation N)]
    [Valuation.HasExtension (ValuativeRel.valuation M) (ValuativeRel.valuation N)]
    [IsIntegralClosure 𝒪[E] 𝒪[K] E] [Module.Finite 𝒪[K] 𝒪[E]]
    [LocalFieldTheory.ValuativeExtension K M] [IsIntegralClosure 𝒪[M] 𝒪[K] M]
    [Module.Finite 𝒪[K] 𝒪[M]]
    [LocalFieldTheory.ValuativeExtension E N] [IsIntegralClosure 𝒪[N] 𝒪[E] N]
    [Module.Finite 𝒪[E] 𝒪[N]]
    [IsUnramifiedValuedExtension K M] [IsUnramifiedValuedExtension E N]

omit [IsUniformAddGroup M] [IsUniformAddGroup N]
  [IsIntegralClosure 𝒪[E] 𝒪[K] E] [Module.Finite 𝒪[K] 𝒪[E]]
  [LocalFieldTheory.ValuativeExtension K M] [LocalFieldTheory.ValuativeExtension E N] in
/-- A relative arithmetic Frobenius restricts to the power indexed by the
actual residue extension of the two bases. -/
theorem restrictNormal_arithmeticFrobenius_eq_pow_residueFinrank :
    ((arithmeticFrobeniusOfUnramifiedValuation E N).restrictScalars K).restrictNormal M =
      arithmeticFrobeniusOfUnramifiedValuation K M ^ finrank 𝓀[K] 𝓀[E] := by
  let σ := arithmeticFrobeniusOfUnramifiedValuation E N
  let τ := arithmeticFrobeniusOfUnramifiedValuation K M
  let f := finrank 𝓀[K] 𝓀[E]
  let ρ := galoisGroupResidueAlgEquivHomOfIsIntegralClosure K M
  let : Fintype 𝓀[K] := Fintype.ofFinite 𝓀[K]
  let : Fintype 𝓀[E] := Fintype.ofFinite 𝓀[E]
  have hcard : Nat.card 𝓀[E] = Nat.card 𝓀[K] ^ f := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := 𝓀[K])]
  have hτpow (m : ℕ) (x : 𝓀[M]) : (ρ (τ ^ m)) x = x ^ (Nat.card 𝓀[K] ^ m) := by
    induction m with
    | zero => simp only [pow_zero, map_one, AlgEquiv.one_apply, pow_one]
    | succ m ih =>
      rw [pow_succ', map_mul, AlgEquiv.mul_apply, ih]
      change galoisGroupResidueAlgEquivOfIsIntegralClosure K M τ
        (x ^ (Nat.card 𝓀[K] ^ m)) = x ^ (Nat.card 𝓀[K] ^ (m + 1))
      rw [galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply,
        ← pow_mul, pow_succ]
  apply (galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation K M)
  apply AlgEquiv.ext
  intro x
  apply (algebraMap 𝓀[M] 𝓀[N]).injective
  change algebraMap 𝓀[M] 𝓀[N] (galoisGroupResidueAlgEquivOfIsIntegralClosure K M
    ((σ.restrictScalars K).restrictNormal M) x) = algebraMap 𝓀[M] 𝓀[N] ((ρ (τ ^ f)) x)
  rw [galoisGroupResidue_restrictNormal_commutes K E M N,
    galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply, hτpow, map_pow, hcard]

/-- For a finite tower where the relative unramified degree is the lower
unramified degree divided by the base residue degree, the actual restriction
of a relative Brauer class multiplies its invariant by the base field degree. -/
theorem unramifiedInvariant_tower_restriction
    (hdegree : finrank K M = finrank 𝓀[K] 𝓀[E] * finrank E N)
    (x : groupCohomology (liftedGaloisUnitsRep K M) 2) :
    unramifiedInvariant E N (liftedFiniteGaloisTowerUnitsH2Restriction K E N
      (liftedFiniteGaloisTowerUnitsH2Inflation K M N x)) =
      finrank K E • unramifiedInvariant K M x := by
  let : IsCyclic Gal(M/K) := isCyclic_galoisGroup_of_unramifiedValuation K M
  let : IsCyclic Gal(N/E) := isCyclic_galoisGroup_of_unramifiedValuation E N
  obtain ⟨a, ha⟩ := unramifiedClass_surjective K M x
  let f := finrank 𝓀[K] 𝓀[E]
  let aE := mapBaseUnitsToExtensionUnits K E a.toMul
  have hcard : Nat.card Gal(M/K) = f * Nat.card Gal(N/E) := by
    rw [IsGalois.card_aut_eq_finrank K M, IsGalois.card_aut_eq_finrank E N]
    exact hdegree
  have hclass := liftedCyclicBaseUnitH2Class_inflation_restriction_eq_class K M E N
    (arithmeticFrobeniusOfUnramifiedValuation K M)
    (arithmeticFrobeniusOfUnramifiedValuation_generates K M)
    (arithmeticFrobeniusOfUnramifiedValuation E N)
    (arithmeticFrobeniusOfUnramifiedValuation_generates E N)
    f Module.finrank_pos hcard
    (restrictNormal_arithmeticFrobenius_eq_pow_residueFinrank K E M N) a.toMul
  have hactual : liftedFiniteGaloisTowerUnitsH2Restriction K E N
      (liftedFiniteGaloisTowerUnitsH2Inflation K M N x) =
        unramifiedClass E N (Additive.ofMul aE) := by
    rw [← ha]
    change liftedFiniteGaloisTowerUnitsH2Restriction K E N
      (liftedFiniteGaloisTowerUnitsH2Inflation K M N
        (unramifiedClass K M (Additive.ofMul a.toMul))) = _
    rw [unramifiedClass_apply K M, unramifiedClass_apply E N]
    exact hclass
  have hmax : (𝓂[K] : Ideal 𝒪[K]) ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField
    (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]) (IsDiscreteValuationRing.not_isField 𝒪[K])
  let e := (𝓂[E] : Ideal 𝒪[E]).ramificationIdx 𝒪[K]
  have hef : e * f = finrank K E := by
    simpa only [e, f, Ideal.ramificationIdx'_eq_ramificationIdx _ _ hmax] using
      maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank K E
  rw [hactual, ← ha]
  change unramifiedInvariant E N (unramifiedClass E N (Additive.ofMul aE)) =
    finrank K E • unramifiedInvariant K M (unramifiedClass K M (Additive.ofMul a.toMul))
  rw [unramifiedInvariant_class E N, unramifiedInvariant_class K M, ← AddCircle.coe_nsmul,
    valuationMap_apply, valuationMap_apply,
    v_mapBaseUnitsToExtensionUnits_eq_ramificationIdx_mul K E,
    ← mul_neg, Int.cast_mul, Int.cast_natCast, nsmul_eq_mul, ← hef, hdegree,
    Nat.cast_mul, Nat.cast_mul]
  apply congrArg (fun q : ℚ => (q : AddCircle (1 : ℚ)))
  have hf : (f : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hN : (finrank E N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  dsimp only [e, f] at hf ⊢
  field_simp [hf, hN]

end Ordinary

section Continuous

variable (K : Type u) (E M N : Type v)
    [Field K] [Field E] [Field M] [Field N]
    [Algebra K E] [Algebra K M] [Algebra K N] [Algebra E N] [Algebra M N]
    [IsScalarTower K E N] [IsScalarTower K M N]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeRel M] [UniformSpace M] [IsUniformAddGroup M] [IsNonarchimedeanLocalField M]
    [ValuativeRel N] [UniformSpace N] [IsUniformAddGroup N] [IsNonarchimedeanLocalField N]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    [FiniteDimensional K M] [IsGalois K M] [FiniteDimensional K N]
    [FiniteDimensional E N] [IsGalois E N]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E)]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation M)]
    [Valuation.HasExtension (ValuativeRel.valuation E) (ValuativeRel.valuation N)]
    [Valuation.HasExtension (ValuativeRel.valuation M) (ValuativeRel.valuation N)]
    [IsIntegralClosure 𝒪[E] 𝒪[K] E] [Module.Finite 𝒪[K] 𝒪[E]]
    [LocalFieldTheory.ValuativeExtension K M]
    [IsIntegralClosure 𝒪[M] 𝒪[K] M] [Module.Finite 𝒪[K] 𝒪[M]]
    [LocalFieldTheory.ValuativeExtension E N]
    [IsIntegralClosure 𝒪[N] 𝒪[E] N] [Module.Finite 𝒪[E] 𝒪[N]]
    [IsUnramifiedValuedExtension K M] [IsUnramifiedValuedExtension E N]

/-- Inflation followed by base restriction multiplies the continuous unramified invariant
by the base extension degree under the corresponding unramified degree relation. -/
theorem unramifiedContinuousInvariant_tower_restriction
    (hdegree : finrank K M = finrank 𝓀[K] 𝓀[E] * finrank E N)
    (x : continuousCohomology 2 (galoisUnitsRep K M)) :
    unramifiedContinuousInvariant E N (relativeBaseRestriction K E N (relativeInflation K M N x)) =
      finrank K E • unramifiedContinuousInvariant K M x := by
  change unramifiedInvariant E N (continuousRelativeUnitsH2Equiv E N
      (relativeBaseRestriction K E N (relativeInflation K M N x))) =
    finrank K E • unramifiedInvariant K M (continuousRelativeUnitsH2Equiv K M x)
  rw [continuousRelativeUnitsH2Equiv_baseRestriction, continuousRelativeUnitsH2Equiv_inflation]
  exact unramifiedInvariant_tower_restriction K E M N hdegree _

end Continuous

end ClassFieldTheory.Brauer

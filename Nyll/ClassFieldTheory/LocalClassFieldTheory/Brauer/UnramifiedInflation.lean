/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.ContinuousUnramified
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedComparison
public import Nyll.GaloisCohomology.Kummer.LiftedFiniteGaloisTowerUnitsH2
public import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryInflation

/-!
# Compatibility of arithmetic invariants in unramified towers

Arithmetic Frobenius at both stages is the restriction of the same
degree-one absolute automorphism. Inflation multiplies the carry
coefficient by the relative degree, which cancels from the normalized value.
-/

@[expose] public section

open scoped ValuativeRel
open CategoryTheory ClassFormation ClassFieldTower.Cohomology RamificationTheory
open LocalClassFieldTheory LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable section

namespace ClassFieldTheory.Brauer

universe u v

variable (K : Type u) (L M : Type v) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [ValuativeRel M] [UniformSpace M] [IsUniformAddGroup M] [IsNonarchimedeanLocalField M]
    [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K L] [IsGalois K M]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation M)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.ValuativeExtension K M] [IsIntegralClosure 𝒪[M] 𝒪[K] M]
    [Module.Finite 𝒪[K] 𝒪[M]]
    [IsUnramifiedValuedExtension K L] [IsUnramifiedValuedExtension K M]

omit [IsUniformAddGroup L] [IsUniformAddGroup M]
  [LocalFieldTheory.ValuativeExtension K L] [LocalFieldTheory.ValuativeExtension K M] in
/-- Restriction in an actual unramified tower preserves arithmetic Frobenius. -/
theorem restrictNormalHom_arithmeticFrobenius :
    AlgEquiv.restrictNormalHom L (arithmeticFrobeniusOfUnramifiedValuation K M) =
      arithmeticFrobeniusOfUnramifiedValuation K L := by
  let j : M →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let i : L →ₐ[K] SeparableClosure K := j.comp (IsScalarTower.toAlgHom K L M)
  obtain ⟨σ, hσ⟩ := localResidueDegree_surjective K (Multiplicative.ofAdd (1 : ZHat))
  have hB : σ ∈ (intrinsicAbstractBase K).toSubgroup := by
    change σ ∈ (closedFixingSubgroup K (SeparableClosure K) ⊥).toSubgroup
    rw [closedFixingSubgroup_bot_eq_baseField]
    exact Subgroup.mem_top _
  let τ : (intrinsicAbstractBase K).toSubgroup := ⟨σ, hB⟩
  have hL := finiteGaloisRestriction_eq_arithmeticFrobenius_of_degree_one K L i τ hσ
  have hM := finiteGaloisRestriction_eq_arithmeticFrobenius_of_degree_one K M j τ hσ
  apply AlgEquiv.ext
  intro x
  apply i.injective
  calc
    i (AlgEquiv.restrictNormalHom L (arithmeticFrobeniusOfUnramifiedValuation K M) x) =
      j (arithmeticFrobeniusOfUnramifiedValuation K M (algebraMap L M x)) :=
        congrArg j ((arithmeticFrobeniusOfUnramifiedValuation K M).restrictNormal_commutes L x)
    _ = σ (j (algebraMap L M x)) := by
      rw [← hM]
      exact finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply K M j τ
        (algebraMap L M x)
    _ = i (arithmeticFrobeniusOfUnramifiedValuation K L x) := by
      rw [← hL]
      exact (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply K L i τ x).symm

variable [FiniteDimensional L M]

omit [IsUniformAddGroup L] [IsUniformAddGroup M]
  [LocalFieldTheory.ValuativeExtension K L] [LocalFieldTheory.ValuativeExtension K M] in
/-- Inflation of the actual arithmetic carry class raises its base-unit
coefficient to the relative extension degree. -/
theorem unramifiedClass_inflation (a : Kˣ) :
    liftedFiniteGaloisTowerUnitsH2Inflation K L M (unramifiedClass K L (Additive.ofMul a)) =
      unramifiedClass K M (Additive.ofMul (a ^ Module.finrank L M)) := by
  let : IsCyclic Gal(L/K) := isCyclic_galoisGroup_of_unramifiedValuation K L
  let : IsCyclic Gal(M/K) := isCyclic_galoisGroup_of_unramifiedValuation K M
  let : CommGroup Gal(L/K) := IsCyclic.commGroup
  let : CommGroup Gal(M/K) := IsCyclic.commGroup
  let g := arithmeticFrobeniusOfUnramifiedValuation K L
  let h := arithmeticFrobeniusOfUnramifiedValuation K M
  let hg := arithmeticFrobeniusOfUnramifiedValuation_generates K L
  let hh := arithmeticFrobeniusOfUnramifiedValuation_generates K M
  let f : Gal(M/K) →* Gal(L/K) := AlgEquiv.restrictNormalHom L
  let φ := liftedFiniteGaloisTowerUnitsInflationRepHom K L M
  let d := Module.finrank L M
  let A := liftedGaloisUnitsRep K L
  let B := liftedGaloisUnitsRep K M
  let a₀ := liftedBaseUnitCycle K L g a
  let b₀ := liftedBaseUnitCycle K M h (a ^ d)
  have hf : f h = g := restrictNormalHom_arithmeticFrobenius K L M
  have hcard : Nat.card Gal(M/K) = d * Nat.card Gal(L/K) := by
    rw [galoisGroup_card_eq_finrank_of_unramifiedValuation K M,
      galoisGroup_card_eq_finrank_of_unramifiedValuation K L, Nat.mul_comm]
    exact (Module.finrank_mul_finrank K L M).symm
  change groupCohomology.map f φ 2 (groupCohomology.H2π A (finiteCyclicCarryTwoCocycle A g hg a₀)) =
    groupCohomology.H2π B (finiteCyclicCarryTwoCocycle B h hh b₀)
  apply finiteCyclicCarry_inflation_eq_class g hg h hh f hf A B φ d hcard a₀ b₀
  apply Additive.toMul.injective
  apply Units.ext
  change algebraMap K M ((a : K) ^ d) = (algebraMap L M (algebraMap K L (a : K))) ^ d
  rw [map_pow, ← IsScalarTower.algebraMap_apply K L M]

/-- The finite unramified invariant is independent of enlargement of the
relative layer inside an actual unramified tower. -/
theorem unramifiedInvariant_inflation
    (c : groupCohomology (liftedGaloisUnitsRep K L) 2) :
    unramifiedInvariant K M (liftedFiniteGaloisTowerUnitsH2Inflation K L M c) =
      unramifiedInvariant K L c := by
  obtain ⟨a, rfl⟩ := unramifiedClass_surjective K L c
  change unramifiedInvariant K M
      (liftedFiniteGaloisTowerUnitsH2Inflation K L M
        (unramifiedClass K L (Additive.ofMul a.toMul))) =
    unramifiedInvariant K L (unramifiedClass K L (Additive.ofMul a.toMul))
  rw [unramifiedClass_inflation, unramifiedInvariant_class, unramifiedInvariant_class]
  rw [valuationMap_apply, valuationMap_apply, v_pow, ← mul_neg, Int.cast_mul, Int.cast_natCast,
    ← Module.finrank_mul_finrank K L M, Nat.cast_mul, mul_comm (Module.finrank L M : ℚ)]
  exact congrArg (fun q : ℚ => (q : AddCircle (1 : ℚ)))
    (mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr (Module.finrank_pos (R := L) (M := M)).ne'))

/-- The finite arithmetic invariant is preserved by actual continuous
inflation in the unramified tower. -/
theorem unramifiedContinuousInvariant_inflation
    (c : continuousCohomology 2 (galoisUnitsRep K L)) :
    unramifiedContinuousInvariant K M (relativeInflation K L M c) =
      unramifiedContinuousInvariant K L c := by
  change unramifiedInvariant K M (continuousRelativeUnitsH2Equiv K M (relativeInflation K L M c)) =
    unramifiedInvariant K L (continuousRelativeUnitsH2Equiv K L c)
  rw [continuousRelativeUnitsH2Equiv_inflation, unramifiedInvariant_inflation]

end ClassFieldTheory.Brauer

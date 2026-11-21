/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormalizedIntegerValuation
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
public import Nyll.ValuedFieldTheory.Valuation.LocalRingEquiv
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Units.Equiv

/-!
# Principal units and ideal powers under valuation normalization

Normalizing the value group preserves the integer ring, every maximal-ideal
power, and every principal-unit group, with the same underlying field elements.
-/

@[expose] public section

noncomputable section

namespace LocalFieldTheory

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField
open DiscreteValuationField.MultiplicativeIntegerValuation (completeDVFOfWithZeroValuation)
open DiscreteValuationField.CompleteDVF (higherPrincipalUnitGroup)

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Normalization identifies the actual maximal-ideal powers by the identity
on their underlying field elements. -/
def localIntegerValuationIdealPowEquiv (n : ℕ) :
    let F := completeDVFOfWithZeroValuation (localIntegerValuation K)
    (F.maximalIdeal ^ n : Ideal F.valuationSubring) ≃+ (𝓂[K] ^ n : Ideal 𝒪[K]) := by
  intro F
  let e : F.valuationSubring ≃+* 𝒪[K] :=
    localIntegerValuationSubringEquiv K
  refine
    { toFun := fun x => ⟨e x.1, ?_⟩
      invFun := fun x => ⟨e.symm x.1, ?_⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x.1)
      map_add' := fun x y => Subtype.ext (e.map_add x.1 y.1) }
  · exact (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff e n x.1).2 x.property
  · exact (ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff e.symm n x.1).2 x.property

/-- The ideal-power equivalence preserves field values. -/
@[simp]
theorem localIntegerValuationIdealPowEquiv_apply_coe (n : ℕ)
    (x : ((completeDVFOfWithZeroValuation (localIntegerValuation K)).maximalIdeal ^ n :
      Ideal (completeDVFOfWithZeroValuation (localIntegerValuation K)).valuationSubring)) :
    ((localIntegerValuationIdealPowEquiv K n x).1 : K) = (x.1 : K) :=
  rfl

/-- The inverse ideal-power equivalence preserves field values. -/
@[simp]
theorem localIntegerValuationIdealPowEquiv_symm_apply_coe (n : ℕ)
    (x : (𝓂[K] ^ n : Ideal 𝒪[K])) :
    (((localIntegerValuationIdealPowEquiv K n).symm x).1 : K) = (x.1 : K) :=
  rfl

/-- Normalized principal units identify with the standard subgroup of field
units, without changing any field element. -/
def localIntegerValuationPrincipalUnitsEquiv (n : ℕ) :
    let F := completeDVFOfWithZeroValuation (localIntegerValuation K)
    higherPrincipalUnitGroup F n ≃* fieldPrincipalUnits K n := by
  intro F
  let e : F.valuationSubring ≃+* 𝒪[K] :=
    localIntegerValuationSubringEquiv K
  let eU := Units.mapEquiv e.toMulEquiv
  have hmem (x : F.valuationSubringˣ) :
      eU x ∈ principalUnits K n ↔ x ∈ higherPrincipalUnitGroup F n := by
    change e x.val - 1 ∈
        IsLocalRing.maximalIdeal 𝒪[K] ^ n ↔ _
    rw [← e.map_one, ← e.map_sub]
    exact ValuationTheory.ringEquiv_mem_maximalIdeal_pow_iff e n _
  let eP : higherPrincipalUnitGroup F n ≃* principalUnits K n :=
    { toFun := fun x => ⟨eU x.1, (hmem x.1).2 x.property⟩
      invFun := fun x => ⟨eU.symm x.1, (hmem (eU.symm x.1)).1 (by
        rw [eU.apply_symm_apply]
        exact x.property)⟩
      left_inv := fun x => Subtype.ext (eU.symm_apply_apply x.1)
      right_inv := fun x => Subtype.ext (eU.apply_symm_apply x.1)
      map_mul' := fun x y => Subtype.ext (eU.map_mul x.1 y.1) }
  exact eP.trans ((principalUnits K n).equivMapOfInjective
    (integerUnitsToFieldUnits K) (integerUnitsToFieldUnits_injective K))

/-- The principal-unit equivalence preserves field values. -/
@[simp]
theorem localIntegerValuationPrincipalUnitsEquiv_apply_coe (n : ℕ)
    (x : higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation (localIntegerValuation K)) n) :
    ((localIntegerValuationPrincipalUnitsEquiv K n x).1 : K) = (x.1.val : K) :=
  rfl

/-- The inverse principal-unit equivalence preserves field values. -/
@[simp]
theorem localIntegerValuationPrincipalUnitsEquiv_symm_apply_coe (n : ℕ)
    (x : fieldPrincipalUnits K n) :
    (((localIntegerValuationPrincipalUnitsEquiv K n).symm x).1.val : K) = (x.1 : K) := by
  have h := congrArg (fun y : fieldPrincipalUnits K n => ((y : Kˣ) : K))
    ((localIntegerValuationPrincipalUnitsEquiv K n).apply_symm_apply x)
  simpa only [localIntegerValuationPrincipalUnitsEquiv_apply_coe] using h

end LocalFieldTheory

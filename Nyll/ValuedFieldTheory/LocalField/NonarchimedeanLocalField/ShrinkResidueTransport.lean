/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.Irreducible.Lemmas
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkTransport
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence

/-!
# The actual integer ring and residue field of the small local-field representative

The fixed field equivalence restricts to the valuation rings and descends to their residue fields.
Its effect on the normalized integer valuation is proved from a DVR prime element and the existing
unit/uniformizer decomposition, including the inverse-uniformizer sign convention.
-/

@[expose] public section

noncomputable section

namespace LocalFieldTheory

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The fixed small-field equivalence preserves membership in the actual valuation integer ring. -/
theorem shrinkLocalField_mem_integer_iff :
    let : Small.{0} K := smallLocalField K
    let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    ∀ x : Shrink.{0} K, x ∈ 𝒪[Shrink.{0} K] ↔ Shrink.ringEquiv K x ∈ 𝒪[K] := by
  intro sharedSmall sharedValuation x
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, ← not_lt, ← not_lt]
  apply not_congr
  simpa only [map_one] using shrinkLocalField_valuation_lt_iff K 1 x

/-- Restriction of the same field equivalence to the actual valuation integer rings. -/
def shrinkIntegerRingEquiv :
    let : Small.{0} K := smallLocalField K
    let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    𝒪[Shrink.{0} K] ≃+* 𝒪[K] := by
  intro sharedSmall sharedValuation
  exact {
    toFun := fun x => ⟨Shrink.ringEquiv K x, (shrinkLocalField_mem_integer_iff K x).mp x.2⟩
    invFun := fun x => ⟨(Shrink.ringEquiv K).symm x,
      (shrinkLocalField_mem_integer_iff K _).mpr (by
        rw [RingEquiv.apply_symm_apply]
        exact x.2)⟩
    left_inv := fun x => Subtype.ext ((Shrink.ringEquiv K).symm_apply_apply x)
    right_inv := fun x => Subtype.ext ((Shrink.ringEquiv K).apply_symm_apply x)
    map_mul' := fun x y => Subtype.ext ((Shrink.ringEquiv K).map_mul x y)
    map_add' := fun x y => Subtype.ext ((Shrink.ringEquiv K).map_add x y) }

/-- The integer-ring equivalence is the original field equivalence on underlying elements. -/
theorem shrinkIntegerRingEquiv_coe :
    let : Small.{0} K := smallLocalField K
    let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    ∀ x : 𝒪[Shrink.{0} K], (shrinkIntegerRingEquiv K x : K) = Shrink.ringEquiv K x := by
  intro sharedSmall sharedValuation x
  rfl

/-- The induced equivalence of the actual residue fields. -/
def shrinkResidueFieldEquiv :
    let : Small.{0} K := smallLocalField K
    let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    𝓀[Shrink.{0} K] ≃+* 𝓀[K] := by
  intro sharedSmall sharedValuation
  exact IsLocalRing.ResidueField.mapEquiv (shrinkIntegerRingEquiv K)

/-- Reduction commutes with the fixed integer-ring and residue-field equivalences. -/
theorem shrinkResidueFieldEquiv_residue :
    let : Small.{0} K := smallLocalField K
    let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    ∀ x : 𝒪[Shrink.{0} K],
      shrinkResidueFieldEquiv K (IsLocalRing.residue 𝒪[Shrink.{0} K] x) =
        IsLocalRing.residue 𝒪[K] (shrinkIntegerRingEquiv K x) := by
  intro sharedSmall sharedValuation x
  rfl

/-- The two actual residue fields have the same cardinality. -/
theorem shrinkResidueField_card :
    let : Small.{0} K := smallLocalField K
    let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    Nat.card 𝓀[Shrink.{0} K] = Nat.card 𝓀[K] := by
  intro sharedSmall sharedValuation
  exact Nat.card_congr (shrinkResidueFieldEquiv K).toEquiv

/-- Mapping integer units and then including them agrees with the same field-unit equivalence. -/
theorem shrinkIntegerUnitsToFieldUnits :
    let : Small.{0} K := smallLocalField K
    let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    ∀ x : 𝒪[Shrink.{0} K]ˣ,
      Units.mapEquiv (Shrink.ringEquiv K).toMulEquiv
          (integerUnitsToFieldUnits (Shrink.{0} K) x) =
        integerUnitsToFieldUnits K (Units.mapEquiv (shrinkIntegerRingEquiv K).toMulEquiv x) := by
  intro sharedSmall sharedValuation x
  apply Units.ext
  rfl

/-- The fixed small-field equivalence transports each actual field principal-unit group. -/
theorem fieldPrincipalUnits_map_shrink (n : ℕ) :
    let : Small.{0} K := smallLocalField K
    let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    (fieldPrincipalUnits (Shrink.{0} K) n).map
        (Units.mapEquiv (Shrink.ringEquiv K).toMulEquiv).toMonoidHom =
      fieldPrincipalUnits K n := by
  intro sharedSmall sharedValuation
  have hcomp :
      (Units.mapEquiv (Shrink.ringEquiv K).toMulEquiv).toMonoidHom.comp
          (integerUnitsToFieldUnits (Shrink.{0} K)) =
        (integerUnitsToFieldUnits K).comp
          (Units.mapEquiv (shrinkIntegerRingEquiv K).toMulEquiv).toMonoidHom := by
    apply MonoidHom.ext
    intro a
    exact shrinkIntegerUnitsToFieldUnits K a
  change ((principalUnits (Shrink.{0} K) n).map
    (integerUnitsToFieldUnits (Shrink.{0} K))).map _ =
      (principalUnits K n).map (integerUnitsToFieldUnits K)
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
    principalUnits_map_ringEquiv (Shrink.{0} K) K (shrinkIntegerRingEquiv K) n]

/-- The same field-unit equivalence preserves the actual normalized additive valuation. -/
theorem valuationMap_shrinkRingEquiv :
    let : Small.{0} K := smallLocalField K
    let : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    let : IsNonarchimedeanLocalField (Shrink.{0} K) :=
      shrinkLocalField_isNonarchimedeanLocalField K
    ∀ x : (Shrink.{0} K)ˣ,
      valuationMap K (Additive.ofMul (Units.mapEquiv (Shrink.ringEquiv K).toMulEquiv x)) =
        valuationMap (Shrink.{0} K) (Additive.ofMul x) := by
  intro sharedSmall sharedValuation sharedLocal x
  let e := Units.mapEquiv (Shrink.ringEquiv K).toMulEquiv
  let ϖ := inverseIntegerRingUniformizerFieldUnit (Shrink.{0} K)
  have hϖ : valuationMap (Shrink.{0} K) (Additive.ofMul ϖ) = 1 :=
    v_inverseIntegerRingUniformizerFieldUnit (Shrink.{0} K)
  have hprime : Irreducible
      (shrinkIntegerRingEquiv K (chosenIntegerRingUniformizer (Shrink.{0} K))) :=
    (MulEquiv.irreducible_iff (shrinkIntegerRingEquiv K)).mpr
      (chosenIntegerRingUniformizer_irreducible (Shrink.{0} K))
  have hϖK : valuationMap K (Additive.ofMul (e ϖ)) = 1 := by
    change v K (Additive.ofMul (e ϖ)) = 1
    dsimp only [ϖ]
    rw [inverseIntegerRingUniformizerFieldUnit, map_inv]
    exact v_integerRingIrreducibleFieldUnit_inv K _ hprime
      (e (integerRingUniformizerFieldUnit (Shrink.{0} K))) rfl
  let a := uniformizerUnitFactor (Shrink.{0} K) ϖ hϖ x
  have ha : valuationMap K (Additive.ofMul (e (integerUnitsToFieldUnits (Shrink.{0} K) a))) =
      0 := by
    change valuationMap K (Additive.ofMul
      (Units.mapEquiv (Shrink.ringEquiv K).toMulEquiv
        (integerUnitsToFieldUnits (Shrink.{0} K) a))) = 0
    rw [shrinkIntegerUnitsToFieldUnits K a, valuationMap_apply]
    exact v_integerUnitsToFieldUnits K _
  have hx := congrArg e (uniformizerUnitFactor_mul_uniformizer_zpow
    (Shrink.{0} K) ϖ hϖ x)
  rw [map_mul, map_zpow] at hx
  change valuationMap K (Additive.ofMul (e x)) = _
  rw [← hx, valuationMap_ofMul_mul, ha, valuationMap_ofMul_zpow, hϖK, zero_add, mul_one]

end LocalFieldTheory

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAbelian
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UniformizerNorm
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitTransport
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentUniformizerNormalization
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence

/-!
# Normalization of native Artin on equal-characteristic Lubin--Tate levels

The actual prime-element norm proves that the Laurent parameter and its
inverse have trivial native Artin image. Hence the native Artin value of an
arbitrary field unit equals that of its valuation-zero factor. The changed
parameter `aT` has the same image as `a`.

No comparison with an explicit bracket automorphism is used or asserted.
-/

@[expose] public section

noncomputable section

open scoped LaurentSeries PowerSeries

universe u v

namespace LocalClassFieldTheory

open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.IsNonarchimedeanLocalField
open LubinTate.EqualCharacteristic

variable {K : Type u} [Field K]

/-- The ordinary Laurent parameter is an actual norm from each finite
Lubin--Tate level, so its native Artin image is trivial. -/
theorem equalCharacteristicAbelianLocalArtin_uniformizer
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic] (n : ℕ) :
    let B := F.residueField⸨X⸩
    let L := equalCharacteristicLubinTateLevelField F n
    let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let : FiniteDimensional B L :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    Universe.abelianLocalArtinMonoidHom B L
      (equalCharacteristicLaurentUniformizerUnit F) = 1 := by
  intro B L valuationOwner localFieldOwner finiteOwner
  have hnormInv :=
    equalCharacteristicLubinTate_normalizedUniformizer_mem_normSubgroup F n
  have hnorm := (equalCharacteristicLubinTateNormSubgroup F n).inv_mem hnormInv
  rw [inv_inv] at hnorm
  change equalCharacteristicLaurentUniformizerUnit F ∈ localNormSubgroup B L at hnorm
  rw [← Universe.abelianLocalArtinMonoidHom_ker, MonoidHom.mem_ker] at hnorm
  exact hnorm

/-- The normalized parameter `T⁻¹` has the same trivial native Artin image.
Both signs are visible; no Frobenius convention is silently changed. -/
theorem equalCharacteristicAbelianLocalArtin_normalizedUniformizer
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic] (n : ℕ) :
    let B := F.residueField⸨X⸩
    let L := equalCharacteristicLubinTateLevelField F n
    let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let : FiniteDimensional B L :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    Universe.abelianLocalArtinMonoidHom B L
      (equalCharacteristicLaurentUniformizerUnit F)⁻¹ = 1 := by
  intro B L valuationOwner localFieldOwner finiteOwner
  rw [map_inv, equalCharacteristicAbelianLocalArtin_uniformizer F n, inv_one]

/-- Multiplying a power-series unit by the Laurent parameter leaves its
native Artin value unchanged on the finite Lubin--Tate level. -/
theorem equalCharacteristicAbelianLocalArtin_changedUniformizer
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    let B := F.residueField⸨X⸩
    let L := equalCharacteristicLubinTateLevelField F n
    let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let : FiniteDimensional B L :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    Universe.abelianLocalArtinMonoidHom B L
        (equalCharacteristicChangedLaurentUniformizerUnit F a) =
      Universe.abelianLocalArtinMonoidHom B L
        (equalCharacteristicPowerSeriesUnitToLaurentFieldUnit F a) := by
  intro B L valuationOwner localFieldOwner finiteOwner
  rw [equalCharacteristicChangedLaurentUniformizerUnit_eq_unit_mul, map_mul,
    equalCharacteristicAbelianLocalArtin_uniformizer F n, mul_one,
    equalCharacteristicPowerSeriesUnitToLaurentFieldUnit_apply]

/-- Removing the actual normalized uniformizer power from a Laurent field
unit preserves its native Artin value on each finite Lubin--Tate level. -/
theorem equalCharacteristicAbelianLocalArtin_eq_uniformizerUnitFactor
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (n : ℕ) (x : F.residueField⸨X⸩ˣ) :
    let B := F.residueField⸨X⸩
    let L := equalCharacteristicLubinTateLevelField F n
    let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let : FiniteDimensional B L :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    Universe.abelianLocalArtinMonoidHom B L x =
      Universe.abelianLocalArtinMonoidHom B L
        (integerUnitsToFieldUnits B
          (uniformizerUnitFactor B (equalCharacteristicLaurentUniformizerUnit F)⁻¹
            (equalCharacteristicLaurentUniformizerUnit_inv_valuationMap F) x)) := by
  intro B L valuationOwner localFieldOwner finiteOwner
  rw [integerUnitsToFieldUnits_uniformizerUnitFactor, map_div, map_zpow,
    equalCharacteristicAbelianLocalArtin_normalizedUniformizer F n,
    one_zpow, div_one]

end LocalClassFieldTheory

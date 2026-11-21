/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteArtinRestriction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.EqualCharacteristicPointwiseArtinComparison
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.PadicMultiplicativeArtinComparison

/-!
# Absolute Artin on explicit Lubin–Tate roots

The same absolute Artin map acts on the multiplicative primitive roots over
`ℚ_[p]` and on the equal-characteristic primitive points over a Laurent-series
field. These finite levels are subfields of the separable closure used for
absolute reciprocity.
-/

@[expose] public section

noncomputable section

open scoped LaurentSeries PowerSeries ValuativeRel

namespace LocalClassFieldTheory

open ClassFieldTower.Martinet.Shafarevich
open LubinTate LubinTate.EqualCharacteristic
open LocalFieldTheory LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open ValuationTheory.DiscreteValuationField

universe u v

/-- The actual absolute Artin symbol acts on the equal-characteristic
primitive point by the direct bracket of the Laurent unit factor. -/
theorem equalCharacteristicAbsoluteLocalArtin_apply_primitiveRoot
    {K : Type u} [Field K] (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (n : ℕ) (x : F.residueField⸨X⸩ˣ) :
    let B := F.residueField⸨X⸩
    let T := equalCharacteristicLubinTateLevelField F n
    let : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField B := equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let : FiniteDimensional B T := equalCharacteristicLubinTateLevelField_finiteDimensional F n
    ((absoluteAbelianRestriction B T
      (absoluteGaloisGroupAbelianizationEquivSeparable B (absoluteLocalArtinMap B x)))
      (equalCharacteristicLubinTateLevelPowerBasis F n).gen : SeparableClosure B) =
      equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        (equalCharacteristicLaurentPowerSeriesUnitPart F x : F.residueField⟦X⟧)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) := by
  intro B T valuationOwner localFieldOwner finiteOwner
  rw [absoluteLocalArtinMap_restriction B T x]
  have hx : abelianLocalArtinMap B T x = abelianLocalArtinMonoidHom B T x :=
    DFunLike.congr_fun (abelianLocalArtinMap_toMonoidHom B T) x
  rw [hx]
  exact equalCharacteristicAbelianLocalArtin_laurentUnit_apply_primitiveRoot F n x

/-- The same absolute map acts on the genuine p-adic cyclotomic root by
the residue of the valuation-zero factor of an arbitrary field unit. -/
theorem padicMultiplicativeAbsoluteLocalArtin_apply_primitiveRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ) (x : ℚ_[p]ˣ) :
    let F := padicLocalField p
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let T := standardLubinTateLevelField hπ n
    let : FiniteDimensional ℚ_[p] T := standardLubinTateLevelField_finiteDimensional hπ n
    let : IsAbelianGalois ℚ_[p] T := standardLubinTateLevelField_isAbelianGalois F hπ n
    let u := CompleteDVF.higherPrincipalUnitGroup.fieldUnitUniformizerUnitPart
      F.toCompleteDVF hπ x
    absoluteAbelianRestriction ℚ_[p] T
        (absoluteGaloisGroupAbelianizationEquivSeparable ℚ_[p]
          (absoluteLocalArtinMap ℚ_[p] x)) (padicMultiplicativePrimitiveRoot p n) =
      (padicMultiplicativePrimitiveRoot p n) ^
        (PadicInt.toZModPow (n + 1)
          ((padicIntEquivValuationSubring p).symm (u : F.valuationSubring))).val := by
  intro F hπ T finiteOwner abelianOwner u
  rw [absoluteLocalArtinMap_restriction ℚ_[p] T x]
  change (abelianLocalArtinMap ℚ_[p] T).toMonoidHom x
    (padicMultiplicativePrimitiveRoot p n) = _
  rw [abelianLocalArtinMap_toMonoidHom,
    padicMultiplicativeAbelianLocalArtin_eq_uniformizerUnitPart p n x]
  exact padicMultiplicativeAbelianLocalArtin_primitiveRoot p n u

end LocalClassFieldTheory

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveAction
public import Nyll.ValuedFieldTheory.Valuation.ValuedAdicComplete
public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Complete discrete valuations on the completed equal-characteristic levels

The completed coefficient field retains its actual Laurent valuation.
The finite splitting field is equipped with the complete discrete valuation
supplied by its integral closure over that Laurent valuation ring. Its
extension property, integral-closure identity and fundamental ramification
identity come from the same chosen valuation.
-/

@[expose] public section

noncomputable section

open scoped LaurentSeries WithZero

universe u v w

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} [Field K]

/-- The completed coefficient field with its existing Laurent valuation. -/
noncomputable def equalCharacteristicCompletedUnramifiedCompleteDVF
    (k : Type w) [Field k] :
    CompleteDVF.{w, 0} (equalCharacteristicCompletedUnramifiedField k) := by
  let : (Valued.v : Valuation
      (equalCharacteristicCompletedUnramifiedField k) ℤᵐ⁰).IsNontrivial :=
    equalCharacteristicCompletedBaseValuationIsNontrivial k
  let : (Valued.v : Valuation
      (equalCharacteristicCompletedUnramifiedField k) ℤᵐ⁰).IsRankOneDiscrete :=
    Valuation.IsRankOneDiscrete.mk' _
  exact ValuationTheory.Valuations.completeDVFOfCompleteValuedField

/-- This package retains the Laurent valuation, without changing its values. -/
@[simp]
theorem equalCharacteristicCompletedUnramifiedCompleteDVF_valuation
    (k : Type w) [Field k] :
    (equalCharacteristicCompletedUnramifiedCompleteDVF k).valuation =
      (Valued.v : Valuation (equalCharacteristicCompletedUnramifiedField k) ℤᵐ⁰) :=
  rfl

/-- The completed primitive splitting field is genuinely Galois: its defining
polynomial is separable. -/
instance equalCharacteristicCompletedLevelField_isGalois
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsGalois (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) := by
  change IsGalois (equalCharacteristicCompletedUnramifiedField F.residueField)
    (equalCharacteristicCompletedPrimitivePolynomial F n).SplittingField
  exact IsGalois.of_separable_splitting_field
    (equalCharacteristicCompletedPrimitivePolynomial_separable F n)

/-- The actual integral closure supplies a complete valuation and all its
finite-extension certificates together. -/
theorem equalCharacteristicCompletedLevelCompleteDVFData_exists
    (F : LocalField.{u, v} K) (n : ℕ) :
    ∃ target : CompleteDVF.{u, 0} (equalCharacteristicCompletedLevelField F n),
      ∃ hExt :
          (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).valuation.HasExtension
            target.valuation,
        let : Valuation.HasExtension
            (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).valuation
              target.valuation := hExt
        IsIntegralClosure target.valuationSubring
            (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).valuationSubring
            (equalCharacteristicCompletedLevelField F n) ∧
          degree
              (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).toDVF
              target.toDVF =
            ramificationIndex
                (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).toDVF
                target.toDVF *
              residueDegree
                (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).toDVF
                target.toDVF :=
  exists_integralClosure_standard_fundamental_identity
    (K := equalCharacteristicCompletedUnramifiedField F.residueField)
    (L := equalCharacteristicCompletedLevelField F n)
    (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField)

/-- The completed level with the valuation from its actual integral closure. -/
noncomputable def equalCharacteristicCompletedLevelCompleteDVF
    (F : LocalField.{u, v} K) (n : ℕ) :
    CompleteDVF.{u, 0} (equalCharacteristicCompletedLevelField F n) :=
  Classical.choose (equalCharacteristicCompletedLevelCompleteDVFData_exists F n)

/-- The selected level valuation extends the original coefficient valuation. -/
theorem equalCharacteristicCompletedLevelCompleteDVF_hasExtension
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).valuation.HasExtension
      (equalCharacteristicCompletedLevelCompleteDVF F n).valuation :=
  Classical.choose
    (Classical.choose_spec (equalCharacteristicCompletedLevelCompleteDVFData_exists F n))

noncomputable instance equalCharacteristicCompletedLevelCompleteDVF_hasExtensionInstance
    (F : LocalField.{u, v} K) (n : ℕ) :
    (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).valuation.HasExtension
      (equalCharacteristicCompletedLevelCompleteDVF F n).valuation :=
  equalCharacteristicCompletedLevelCompleteDVF_hasExtension F n

/-- The selected level valuation ring is the actual integral closure. -/
theorem equalCharacteristicCompletedLevelCompleteDVF_isIntegralClosure
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsIntegralClosure
      (equalCharacteristicCompletedLevelCompleteDVF F n).valuationSubring
      (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).valuationSubring
      (equalCharacteristicCompletedLevelField F n) :=
  (Classical.choose_spec
    (Classical.choose_spec (equalCharacteristicCompletedLevelCompleteDVFData_exists F n))).1

/-- The fundamental identity for the very same selected extension valuation. -/
theorem equalCharacteristicCompletedLevelCompleteDVF_fundamental_identity
    (F : LocalField.{u, v} K) (n : ℕ) :
    degree (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).toDVF
        (equalCharacteristicCompletedLevelCompleteDVF F n).toDVF =
      ramificationIndex
          (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).toDVF
          (equalCharacteristicCompletedLevelCompleteDVF F n).toDVF *
        residueDegree
          (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).toDVF
          (equalCharacteristicCompletedLevelCompleteDVF F n).toDVF :=
  (Classical.choose_spec
    (Classical.choose_spec (equalCharacteristicCompletedLevelCompleteDVFData_exists F n))).2

end EqualCharacteristic
end LubinTate

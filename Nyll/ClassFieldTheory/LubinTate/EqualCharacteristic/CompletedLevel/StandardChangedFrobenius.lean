/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.StandardChangedResidue

/-!
# The actual relative completed Frobenius is inverse arithmetic Frobenius

Reduction through the actual ambient residue embedding identifies the inverse
completed Frobenius with inverse residue arithmetic Frobenius. The already
proved unramifiedness makes the Galois residue action injective, so this is an
equality of the original relative field automorphisms.
-/

@[expose] public section

noncomputable section

open scoped LaurentSeries PowerSeries ValuativeRel

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

noncomputable local instance standardChangedFrobeniusLevelAlgebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra F.residueField⸨X⸩ (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedLevelLaurentAlgebra F n

/-- The actual relative inverse completed Frobenius equals inverse arithmetic
Frobenius for the canonical unramified extension of the changed fixed field. -/
theorem equalCharacteristicRelativeInverseFrobenius_eq_inverseArithmeticFrobenius
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ) :
    let : ValuativeRel F.residueField⸨X⸩ := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField F.residueField⸨X⸩ :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let D := equalCharacteristicCompletedFrobeniusFixedField F a n
    let : NontriviallyNormedField D := finiteExtensionSpectralNormedField F.residueField⸨X⸩ D
    let : ValuativeRel D := finiteExtensionSpectralValuativeRel F.residueField⸨X⸩ D
    let : IsNonarchimedeanLocalField D :=
      finiteExtensionSpectralIsNonarchimedeanLocalField F.residueField⸨X⸩ D
    let M := equalCharacteristicCompletedStandardChangedCompositum F a n
    let : NontriviallyNormedField M := finiteExtensionSpectralNormedField F.residueField⸨X⸩ M
    let : ValuativeRel M := finiteExtensionSpectralValuativeRel F.residueField⸨X⸩ M
    let : IsNonarchimedeanLocalField M :=
      finiteExtensionSpectralIsNonarchimedeanLocalField F.residueField⸨X⸩ M
    let : Valuation.HasExtension (ValuativeRel.valuation D) (ValuativeRel.valuation M) :=
      finiteExtensionSpectralValuation_hasExtension_of_tower F.residueField⸨X⸩ D M
    let : IsIntegralClosure 𝒪[M] 𝒪[D] M :=
      localCompleteDVF_integerRing_isIntegralClosure D M
    let : Module.Finite 𝒪[D] 𝒪[M] := localCompleteDVF_integerRing_moduleFinite D M
    let : IsNonarchimedeanLocalField.IsUnramifiedValuedExtension D M :=
      equalCharacteristicCompletedStandardChangedCompositum_isUnramifiedValuedExtension F a n
    equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius F a n =
      (arithmeticFrobeniusOfUnramifiedValuation D M)⁻¹ := by
  intro baseValuation baseLocalField D changedNorm changedValuation changedLocalField
    M compositumNorm compositumValuation compositumLocalField extension integralClosure
    finiteIntegers unramified
  let τ := equalCharacteristicCompletedStandardChangedRelativeInverseFrobenius F a n
  let embedding := equalCharacteristicCompletedFiniteSubfieldResidueEmbedding F n M
  let completedFrobenius := IsLocalRing.ResidueField.mapEquiv
    (equalCharacteristicCompletedFrobeniusIntegerEquiv F n a⁻¹)
  let residueFrobenius := residueExtensionArithmeticFrobeniusOfValuationExtension D M
  have hcard : Nat.card 𝓀[D] = Nat.card F.residueField :=
    equalCharacteristicCompletedFrobeniusFixedField_residueField_card F a n
  have hpower (x : 𝓀[M]) :
      residueFrobenius x = x ^ Nat.card F.residueField := by
    rw [show residueFrobenius =
        residueExtensionArithmeticFrobeniusOfValuationExtension D M by rfl,
      residueExtensionArithmeticFrobeniusOfValuationExtension_apply, hcard]
  apply galoisGroupResidueAlgEquivHomOfIsIntegralClosure_injective_of_unramifiedValuation D M
  simp only [map_inv, galoisGroupResidueAlgEquivHomOfIsIntegralClosure_apply,
    galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius]
  apply AlgEquiv.ext
  intro x
  apply embedding.injective
  change embedding (galoisGroupResidueFieldEquivOfIsIntegralClosure D M τ x) =
    embedding (residueFrobenius.symm x)
  have hcompat := equalCharacteristicCompositumResidueEmbedding_inverseFrobenius F a n x
  change embedding (galoisGroupResidueFieldEquivOfIsIntegralClosure D M τ x) =
    completedFrobenius.symm (embedding x) at hcompat
  refine hcompat.trans ?_
  apply completedFrobenius.injective
  rw [RingEquiv.apply_symm_apply]
  change embedding x =
    IsLocalRing.ResidueField.mapEquiv
      (equalCharacteristicCompletedFrobeniusIntegerEquiv F n a⁻¹)
      (embedding (residueFrobenius.symm x))
  rw [equalCharacteristicCompletedFrobeniusIntegerEquiv_residue_apply_eq_pow,
    ← map_pow, ← hpower, AlgEquiv.apply_symm_apply]

end EqualCharacteristic
end LubinTate

end

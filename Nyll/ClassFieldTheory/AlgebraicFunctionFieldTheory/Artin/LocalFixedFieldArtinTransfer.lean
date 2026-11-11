/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldContinuousNaturality
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.IntrinsicFrobeniusArtinComparison
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.PrimeComparison
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldNormResidueNaturality
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Actual local Artin maps and transfer in finite fixed-field towers

The finite transfer-inclusion square is expressed using the original
local Artin homomorphisms of the actual fixed fields. Both norm-residue
comparisons come from the local reciprocity theorem. The required
separable-closure equivalences are constructed from the original field
inclusions; no reciprocity compatibility is an input.

The multiplicative form retains the literal inclusion of field units.
The inverse-input form is the convention used by the function-field
one-place Artin maps.
-/

@[expose] public section

noncomputable section

namespace LocalClassFieldTheory

open ClassFormation LocalFieldTheory RamificationTheory KummerTheory CyclicCohomology
open scoped ValuativeRel

private def localFixedFieldClosureEquiv
    (K : Type) [Field K]
    (H : FiniteAbstractField Gal(SeparableClosure K/K)) :
    intrinsicFixedFieldSeparableClosureEquiv K H := by
  let F := abstractFixedField K (SeparableClosure K) H.field
  let : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  have hsep : Algebra.IsSeparable F (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable K F (SeparableClosure K)
  have hclosure : IsSepClosure F (SeparableClosure K) :=
    ⟨inferInstance, hsep⟩
  exact IsSepClosure.equiv F (SeparableClosure F) (SeparableClosure K)

section Transfer

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H H' : FiniteAbstractField Gal(SeparableClosure K/K))
    (J : ClosedSubgroup Gal(SeparableClosure K/K))
    (hJH' : J.toSubgroup ≤ H'.field.toSubgroup)
    (hH'H : H'.field.toSubgroup ≤ H.field.toSubgroup)
    [hNormal : (extensionSubgroup H.field J (hJH'.trans hH'H)).Normal]
    [hFinite : Finite (H.field.toSubgroup ⧸
      extensionSubgroup H.field J (hJH'.trans hH'H))]

local instance localTransfer_lowerAbsoluteFinite :
    Finite ((baseField Gal(SeparableClosure K/K)).toSubgroup ⧸
      extensionSubgroup (baseField Gal(SeparableClosure K/K))
        H.field (le_baseField H.field)) := H.finite

local instance localTransfer_upperAbsoluteFinite :
    Finite ((baseField Gal(SeparableClosure K/K)).toSubgroup ⧸
      extensionSubgroup (baseField Gal(SeparableClosure K/K))
        H'.field (le_baseField H'.field)) := H'.finite

include H hH'H hNormal in
omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] hFinite in
/-- Normality descends to the relative extension above the intermediate fixed field. -/
theorem localTransfer_upperNormal :
    (extensionSubgroup H'.field J hJH').Normal :=
  transferNormNaturality_intermediateExtension_normal H.field H'.field J hJH' hH'H

include H hH'H hFinite in
omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] hNormal in
/-- The relative extension above the intermediate fixed field has finite degree. -/
theorem localTransfer_upperFinite :
    Finite (H'.field.toSubgroup ⧸ extensionSubgroup H'.field J hJH') :=
  FiniteGaloisSubextension.finite_extension_over_intermediate
    (hJH'.trans hH'H) hH'H hJH'

/-- The original finite local Artin maps commute with the original
abelianized relative transfer and actual fixed-field inclusion. -/
theorem intrinsicFixedFieldLocalArtin_transfer_inclusion :
    let : (extensionSubgroup H'.field J hJH').Normal :=
      localTransfer_upperNormal K H H' J hJH' hH'H
    let : Finite (H'.field.toSubgroup ⧸ extensionSubgroup H'.field J hJH') :=
      localTransfer_upperFinite K H H' J hJH' hH'H
    (abstractFixedFieldAbelianizedTransfer
        K (SeparableClosure K) H.field H'.field J hJH' hH'H).comp
      (intrinsicFixedFieldLocalArtinMonoidHom
        K H J (hJH'.trans hH'H)) =
      (intrinsicFixedFieldLocalArtinMonoidHom K H' J hJH').comp
        (abstractFixedFieldUnitsInclusion
          K (SeparableClosure K) H.field H'.field hH'H) := by
  intro hUpperNormal hUpperFinite
  rw [intrinsicFixedFieldLocalArtinMonoidHom_eq_abstractFixedFieldNormResidueSymbol
    K H J (hJH'.trans hH'H) (localFixedFieldClosureEquiv K H),
    intrinsicFixedFieldLocalArtinMonoidHom_eq_abstractFixedFieldNormResidueSymbol
      K H' J hJH' (localFixedFieldClosureEquiv K H')]
  exact abstractFixedFieldNormResidueSymbol_transfer_inclusion
    K (SeparableClosure K) (localResidueDatum K) (localHenselianValuation K)
    (separableClosureUnits_isClassFormation K) H.field H'.field J hJH' hH'H

local notation "F" => abstractFixedField K (SeparableClosure K) (FiniteAbstractField.field H)
local notation "F'" => abstractFixedField K (SeparableClosure K) (FiniteAbstractField.field H')
local notation "E" => abstractRelativeFixedField K (SeparableClosure K) (le_trans hJH' hH'H)
local notation "E'" => abstractRelativeFixedField K (SeparableClosure K) hJH'

local instance localTransfer_lowerFiniteDimensional : FiniteDimensional K F :=
  abstractFixedField_finiteDimensional K (SeparableClosure K) H.field H.finite

local instance localTransfer_upperFiniteDimensional : FiniteDimensional K F' :=
  abstractFixedField_finiteDimensional K (SeparableClosure K) H'.field H'.finite

local instance localTransfer_lowerNormed : NontriviallyNormedField F :=
  finiteExtensionSpectralNormedField K F

local instance localTransfer_upperNormed : NontriviallyNormedField F' :=
  finiteExtensionSpectralNormedField K F'

local instance localTransfer_lowerValuative : ValuativeRel F :=
  finiteExtensionSpectralValuativeRel K F

local instance localTransfer_upperValuative : ValuativeRel F' :=
  finiteExtensionSpectralValuativeRel K F'

local instance localTransfer_lowerLocal : IsNonarchimedeanLocalField F :=
  finiteExtensionSpectralIsNonarchimedeanLocalField K F

local instance localTransfer_upperLocal : IsNonarchimedeanLocalField F' :=
  finiteExtensionSpectralIsNonarchimedeanLocalField K F'

local instance localTransfer_totalFiniteDimensional : FiniteDimensional F E :=
  abstractRelativeFixedField_finiteDimensional K (SeparableClosure K)
    H.field J (hJH'.trans hH'H) H.finite hFinite

include H hH'H hFinite in
omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] hNormal in
/-- The upper relative fixed field is finite-dimensional over its fixed base. -/
theorem localTransfer_relativeFiniteDimensional : FiniteDimensional F' E' :=
  abstractRelativeFixedField_finiteDimensional K (SeparableClosure K)
    H'.field J hJH' H'.finite (localTransfer_upperFinite K H H' J hJH' hH'H)

local instance localTransfer_totalGalois : IsGalois F E :=
  abstractRelativeFixedField_isGalois K (SeparableClosure K)
    H.field J (hJH'.trans hH'H) hNormal

include H hH'H hNormal in
omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] hFinite in
/-- The upper relative fixed field is Galois over its fixed base. -/
theorem localTransfer_relativeGalois : IsGalois F' E' :=
  abstractRelativeFixedField_isGalois K (SeparableClosure K)
    H'.field J hJH' (localTransfer_upperNormal K H H' J hJH' hH'H)

/-- On original units, finite relative transfer sends the lower local Artin
value to the upper local Artin value of the literal field inclusion. -/
theorem localArtinMonoidHom_fixedField_transfer (x : Fˣ) :
    let : FiniteDimensional F E := abstractRelativeFixedField_finiteDimensional
      K (SeparableClosure K) H.field J (hJH'.trans hH'H) H.finite hFinite
    let : IsGalois F E := abstractRelativeFixedField_isGalois
      K (SeparableClosure K) H.field J (hJH'.trans hH'H) hNormal
    let : FiniteDimensional F' E' :=
      localTransfer_relativeFiniteDimensional K H H' J hJH' hH'H
    let : IsGalois F' E' := localTransfer_relativeGalois K H H' J hJH' hH'H
    abstractFixedFieldAbelianizedTransferMonoidHom
        K (SeparableClosure K) H.field H'.field J hJH' hH'H
        (localArtinMonoidHom F E x) =
      localArtinMonoidHom F' E'
        (Units.map (IntermediateField.inclusion
          (abstractFixedField_le K (SeparableClosure K) hH'H)).toRingHom x) := by
  intro hLowerDimensional hLowerGalois hUpperDimensional hUpperGalois
  have h := DFunLike.congr_fun
    (intrinsicFixedFieldLocalArtin_transfer_inclusion K H H' J hJH' hH'H)
    (Additive.ofMul x)
  exact congrArg Additive.toMul h

/-- The same actual square with the inverse-input Artin convention used
by the original function-field decomposition homomorphism. -/
theorem localArtinMonoidHom_fixedField_transfer_inv (x : Fˣ) :
    let : FiniteDimensional F E := abstractRelativeFixedField_finiteDimensional
      K (SeparableClosure K) H.field J (hJH'.trans hH'H) H.finite hFinite
    let : IsGalois F E := abstractRelativeFixedField_isGalois
      K (SeparableClosure K) H.field J (hJH'.trans hH'H) hNormal
    let : FiniteDimensional F' E' :=
      localTransfer_relativeFiniteDimensional K H H' J hJH' hH'H
    let : IsGalois F' E' := localTransfer_relativeGalois K H H' J hJH' hH'H
    abstractFixedFieldAbelianizedTransferMonoidHom
        K (SeparableClosure K) H.field H'.field J hJH' hH'H
        (localArtinMonoidHom F E (x⁻¹)) =
      localArtinMonoidHom F' E'
        ((Units.map (IntermediateField.inclusion
          (abstractFixedField_le K (SeparableClosure K) hH'H)).toRingHom x)⁻¹) := by
  intro hLowerDimensional hLowerGalois hUpperDimensional hUpperGalois
  exact (localArtinMonoidHom_fixedField_transfer K H H' J hJH' hH'H (x⁻¹)).trans
    (congrArg (localArtinMonoidHom F' E') (map_inv _ x))

end Transfer

end LocalClassFieldTheory

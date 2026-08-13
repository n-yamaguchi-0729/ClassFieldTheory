import GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealizationSubextension

/-!
# Norm quotients in the compatible Galois realization

This module identifies the abstract fixed fields with the embedded copies of
`K` and `L`, and transports the resulting idèle-class norm quotient and
reciprocity data to the original finite Galois extension.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open CyclicCohomology
open AlgebraicNumberTheory
open LocalClassFieldTheory
open RamificationTheory

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The fixed field of the lower subgroup is the compatible embedded
copy of `K`. -/
theorem numberFieldTowerAbstractBaseField_eq :
    abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L) =
      numberFieldTowerBaseField K L :=
  InfiniteGalois.fixedField_fixingSubgroup
    (numberFieldTowerBaseField K L)

/-- The original base field is canonically equivalent to the actual
fixed field used by the rational class formation. -/
noncomputable def numberFieldTowerAbstractBaseFieldEquiv :
    K ≃ₐ[ℚ]
      abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L) :=
  (numberFieldTowerLowerEmbedding K L).equivFieldRange.trans
    (IntermediateField.equivOfEq
      (numberFieldTowerAbstractBaseField_eq K L).symm)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- After restriction of scalars to `ℚ`, the upper relative fixed field
is the chosen embedded copy of `L`. -/
theorem numberFieldTowerAbstractTopField_restrictScalars_eq :
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)).restrictScalars ℚ =
      numberFieldInRationalSeparableClosure L :=
  InfiniteGalois.fixedField_fixingSubgroup
    (numberFieldInRationalSeparableClosure L)

/-- The original top field is canonically equivalent over `ℚ` to the
actual relative fixed field used by the rational class formation. -/
noncomputable def numberFieldTowerAbstractTopFieldEquiv :
    L ≃ₐ[ℚ]
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)).restrictScalars ℚ :=
  (numberFieldSeparableClosureEmbedding L).equivFieldRange.trans
    (IntermediateField.equivOfEq
      (numberFieldTowerAbstractTopField_restrictScalars_eq K L).symm)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The equivalences from the original number-field tower to its two
abstract fixed fields commute with the tower algebra maps. -/
@[simp]
theorem numberFieldTowerAbstractFieldEquiv_algebraMap
    (x : K) :
    numberFieldTowerAbstractTopFieldEquiv K L
        (algebraMap K L x) =
      algebraMap
        (abstractFixedField ℚ (SeparableClosure ℚ)
          (numberFieldTowerBaseSubgroup K L))
        (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
        (numberFieldTowerAbstractBaseFieldEquiv K L x) := by
  apply Subtype.ext
  calc
    (numberFieldTowerAbstractTopFieldEquiv K L
        (algebraMap K L x)).1 =
        ((numberFieldSeparableClosureEmbedding L).equivFieldRange
          (algebraMap K L x)).1 := by
      rfl
    _ =
        (algebraMap
          (numberFieldTowerBaseField K L)
          (numberFieldInRationalSeparableClosure L)
          ((numberFieldTowerLowerEmbedding K L).equivFieldRange x)).1 :=
      congrArg Subtype.val
        (numberFieldTowerFieldRangeEquiv_algebraMap K L x)
    _ =
        (algebraMap
          (abstractFixedField ℚ (SeparableClosure ℚ)
            (numberFieldTowerBaseSubgroup K L))
          (abstractRelativeFixedField ℚ (SeparableClosure ℚ)
            (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
          (numberFieldTowerAbstractBaseFieldEquiv K L x)).1 := by
      rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The compatible lower subgroup has finite absolute index in the
rational absolute Galois group.  This opaque theorem keeps consumers
from unfolding the bundled finite-abstract-field witness. -/
theorem numberFieldTowerBaseSubgroup_absoluteQuotient_finite :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          (numberFieldTowerBaseSubgroup K L)
          (le_baseField (numberFieldTowerBaseSubgroup K L))) := by
  simpa only [numberFieldTowerFiniteAbstractField] using
    (numberFieldTowerFiniteAbstractField K L).finite

/-- The absolute-index witness used by the tower realization, registered at
its precise quotient type so downstream declarations need not normalize the
bundled finite-abstract-field construction. -/
noncomputable instance (priority := 2000)
    numberFieldTowerBaseSubgroupAbsoluteQuotientFinite :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          (numberFieldTowerBaseSubgroup K L)
          (le_baseField (numberFieldTowerBaseSubgroup K L))) :=
  numberFieldTowerBaseSubgroup_absoluteQuotient_finite K L

/-- The normality witness for the tower realization, registered only at the
specialized extension subgroup. -/
noncomputable instance (priority := 2000)
    numberFieldTowerExtensionSubgroupNormal :
    (extensionSubgroup
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)).Normal :=
  numberFieldTowerExtensionSubgroup_normal K L

/-- The relative-index witness for the tower realization, registered only at
the specialized quotient consumed by `FiniteNormQuotient`. -/
noncomputable instance (priority := 2000)
    numberFieldTowerExtensionQuotientFinite :
    Finite
      ((numberFieldTowerBaseSubgroup K L).toSubgroup ⧸
        extensionSubgroup
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :=
  numberFieldTowerExtensionQuotient_finite K L

/-- The ordinary idele class group of the original base field,
transported to the fixed part of the rational absolute idele-class
representation used by abstract reciprocity. -/
noncomputable def numberFieldTowerIdeleClassEquivAmbientFixed :
    Additive (IdeleClassGroup K) ≃+
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (numberFieldTowerBaseSubgroup K L) := by
  let H := numberFieldTowerBaseSubgroup K L
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H
  letI hHfinite :
      Finite
        ((baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
          extensionSubgroup
            (baseField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
            H (le_baseField H)) := by
    simpa only [H] using
      (numberFieldTowerBaseSubgroup_absoluteQuotient_finite K L)
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H hHfinite
  letI : NumberField F :=
    NumberField.of_module_finite ℚ F
  exact
    (MulEquiv.toAdditive
      (ideleClassCongr
        (numberFieldTowerAbstractBaseFieldEquiv K L))).trans
      (rationalAbstractFixedFieldIdeleClassEquivFixed
        (hfinite := hHfinite) H)

/-- The ordinary norm quotient of the two fixed fields, kept behind a
small type boundary so the two comparison steps can be elaborated in
separate declarations. -/
private noncomputable def numberFieldTowerFixedFieldNormQuotient : Type :=
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ)
      (numberFieldTowerBaseSubgroup K L)
  let E :=
    abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ)
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L)
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ)
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
      (numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L)
      (numberFieldTowerExtensionQuotientFinite K L)
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : NumberField E := NumberField.of_module_finite ℚ E
  Additive
    (IdeleClassGroup F ⧸
      (_root_.ideleClassNorm F E).range)

private noncomputable instance
    numberFieldTowerFixedFieldNormQuotientAddCommGroup :
    AddCommGroup (numberFieldTowerFixedFieldNormQuotient K L) := by
  unfold numberFieldTowerFixedFieldNormQuotient
  infer_instance

/-- First comparison step: abstract finite norms to the ordinary norm
quotient of the realized fixed fields. -/
private noncomputable def
    numberFieldTowerFiniteNormQuotientEquivFixedFieldNormQuotient :
    FiniteNormQuotient rationalIdeleClassRepresentation
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L) ≃+
      numberFieldTowerFixedFieldNormQuotient K L := by
  let H := numberFieldTowerBaseSubgroup K L
  let J := numberFieldTowerTopSubgroup L
  let hJH : J.toSubgroup ≤ H.toSubgroup :=
    numberFieldTowerTopSubgroup_le_baseSubgroup K L
  letI hHfinite :=
    numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L
  let hnormal := numberFieldTowerExtensionSubgroupNormal K L
  letI := hnormal
  letI hrelativeFinite :=
    numberFieldTowerExtensionQuotientFinite K L
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H
  let E :=
    abstractRelativeFixedField ℚ (SeparableClosure ℚ) hJH
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H hHfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H J hJH
      hHfinite hrelativeFinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : NumberField E := NumberField.of_module_finite ℚ E
  change
    FiniteNormQuotient rationalIdeleClassRepresentation
        H J hJH ≃+
      Additive
        (IdeleClassGroup F ⧸
          (_root_.ideleClassNorm F E).range)
  exact
    rationalFiniteNormQuotientEquivIdeleClassNormQuotient
      (hKfinite := hHfinite) (hfinite := hrelativeFinite)
      H J hJH hnormal

/-- Second comparison step: transport the realized fixed-field norm
quotient back to the original number-field tower. -/
private noncomputable def
    numberFieldTowerFixedFieldNormQuotientEquivActualNormQuotient :
    numberFieldTowerFixedFieldNormQuotient K L ≃+
      Additive
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) := by
  let H := numberFieldTowerBaseSubgroup K L
  let J := numberFieldTowerTopSubgroup L
  let hJH : J.toSubgroup ≤ H.toSubgroup :=
    numberFieldTowerTopSubgroup_le_baseSubgroup K L
  letI hHfinite :=
    numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L
  let hnormal := numberFieldTowerExtensionSubgroupNormal K L
  letI := hnormal
  letI hrelativeFinite :=
    numberFieldTowerExtensionQuotientFinite K L
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) H
  let E :=
    abstractRelativeFixedField ℚ (SeparableClosure ℚ) hJH
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H hHfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H J hJH
      hHfinite hrelativeFinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : NumberField E := NumberField.of_module_finite ℚ E
  letI : FiniteDimensional ℚ (E.restrictScalars ℚ) := by
    change FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) J)
    change FiniteDimensional ℚ E
    infer_instance
  letI : NumberField (E.restrictScalars ℚ) :=
    NumberField.of_module_finite ℚ (E.restrictScalars ℚ)
  let hFE : F ≤ E.restrictScalars ℚ :=
    abstractFixedField_le ℚ (SeparableClosure ℚ) hJH
  letI : Algebra F (E.restrictScalars ℚ) :=
    (IntermediateField.inclusion hFE).toRingHom.toAlgebra
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) H J hJH hnormal
  change
    Additive
        (IdeleClassGroup F ⧸
          (_root_.ideleClassNorm F E).range) ≃+
      Additive
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range)
  exact
    MulEquiv.toAdditive
      (ordinaryIdeleClassNormQuotientCongrOfAlgEquiv
        (numberFieldTowerAbstractBaseFieldEquiv K L)
        (numberFieldTowerAbstractTopFieldEquiv K L)
        (numberFieldTowerAbstractFieldEquiv_algebraMap K L)).symm

/-- The abstract finite norm quotient attached to the compatible
fixed-field realization of `L / K` is the ordinary idele-class norm
quotient of the original extension. -/
noncomputable def
    numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient :
    FiniteNormQuotient rationalIdeleClassRepresentation
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L) ≃+
      Additive
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) := by
  exact
    (numberFieldTowerFiniteNormQuotientEquivFixedFieldNormQuotient K L).trans
      (numberFieldTowerFixedFieldNormQuotientEquivActualNormQuotient K L)

end Reciprocity
end GlobalClassFieldTheory

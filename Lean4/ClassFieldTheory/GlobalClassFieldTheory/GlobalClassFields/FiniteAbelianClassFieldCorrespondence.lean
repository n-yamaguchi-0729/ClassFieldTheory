import AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification
import GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassFormation
import GlobalClassFieldTheory.GlobalClassFields.ClassFieldRealization
import GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleClassValuation

/-!
# The ordinary finite abelian class-field correspondence

The abstract finite abelian classification is formulated on the fixed
parts of the rational absolute idele-class representation.  For a finite
abstract base field, the canonical fixed-field comparison transports its
norm subgroups to the ordinary idele class group of the actual fixed
number field.

This file records that transported correspondence.  In particular, the
two lattice formulas are now equalities of ordinary determinant-norm
subgroups: composita correspond to intersections and intersection fields
correspond to products.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open KummerTheory
open LocalClassFieldTheory
open Reciprocity

/-- Fix the rational algebra structure used by every occurrence of the
absolute Galois group in this module. -/
noncomputable local instance (priority := 2000)
    finiteAbelianClassFieldCorrespondence_separableClosureAlgebra :
    Algebra ℚ (SeparableClosure ℚ) :=
  rationalSeparableClosureAlgebra

variable
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))

local instance ordinaryFixedFieldBaseQuotientFinite :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K.field (le_baseField K.field)) :=
  K.finite

noncomputable local instance ordinaryFixedFieldFiniteDimensional :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) K.field K.finite

noncomputable local instance ordinaryFixedFieldNumberField :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field) :=
  NumberField.of_module_finite ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) K.field)

/-- The ordinary idele-class norm subgroup represented by a finite
abelian subextension of a rational absolute fixed field.

The definition transports the abstract norm subgroup through the
canonical equivalence from the ordinary idele class group of the actual
fixed field.  The theorem
`ordinaryIdeleClassNormSubgroup_eq_actualNormRange` below identifies it
with the genuine determinant-norm range of the represented extension. -/
noncomputable def ordinaryIdeleClassNormSubgroup
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    AddSubgroup
      (Additive
        (IdeleClassGroup
          (abstractFixedField
            ℚ (SeparableClosure ℚ) K.field))) := by
  exact
    (L.normSubgroup rationalIdeleClassRepresentation).map
      (rationalAbstractFixedFieldIdeleClassEquivFixed
        K.field).symm.toAddMonoidHom

private theorem ordinaryIdeleClassNormSubgroup_eq_map
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    ordinaryIdeleClassNormSubgroup K L =
      (L.normSubgroup rationalIdeleClassRepresentation).map
        (rationalAbstractFixedFieldIdeleClassEquivFixed
          K.field).symm.toAddMonoidHom :=
  rfl

/-- The transported subgroup is the genuine ordinary
determinant-norm range of the actual relative fixed-field extension. -/
theorem ordinaryIdeleClassNormSubgroup_eq_actualNormRange
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) K.field
    let E :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below
    letI hKfinite : Finite
        ((baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
          CyclicCohomology.extensionSubgroup
            (baseField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
            K.field (le_baseField K.field)) :=
      K.finite
    letI hLfinite : Finite
        (K.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup K.field L.field L.below) :=
      L.finite
    letI : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K.field hKfinite
    letI : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ)
        K.field L.field L.below hKfinite hLfinite
    letI : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional ℚ E :=
      FiniteDimensional.trans ℚ F E
    letI : NumberField F :=
      NumberField.of_module_finite ℚ F
    letI : NumberField E :=
      NumberField.of_module_finite ℚ E
    letI : IsAbelianGalois F E :=
      finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois L
    ordinaryIdeleClassNormSubgroup K L =
      (_root_.ideleClassNorm F E).range.toAddSubgroup := by
  exact
    (ordinaryIdeleClassNormSubgroup_eq_map K L).trans
      (map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
        (hKfinite := K.finite) (hfinite := L.finite)
        K.field L.field L.below L.normal)

/-- Field inclusion is exactly reverse inclusion of the represented
ordinary determinant-norm subgroups. -/
theorem le_iff_ordinaryIdeleClassNormSubgroup_le
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L₁ L₂ : FiniteAbelianSubextension K.field) :
    L₁ ≤ L₂ ↔
      ordinaryIdeleClassNormSubgroup K L₂ ≤
        ordinaryIdeleClassNormSubgroup K L₁ := by
  change
    L₁ ≤ L₂ ↔
      (L₂.normSubgroup rationalIdeleClassRepresentation).map
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            K.field).symm.toAddMonoidHom ≤
        (L₁.normSubgroup rationalIdeleClassRepresentation).map
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            K.field).symm.toAddMonoidHom
  exact
    (FiniteAbelianSubextension.le_iff_normSubgroup_le
      rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
      K L₁ L₂).trans
      (AddSubgroup.map_le_map_iff_of_injective
        (f :=
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            K.field).symm.toAddMonoidHom)
        (rationalAbstractFixedFieldIdeleClassEquivFixed
          K.field).symm.injective).symm

/-- A finite abelian subextension is uniquely determined by its
ordinary idele-class norm subgroup. -/
theorem ordinaryIdeleClassNormSubgroup_injective
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Function.Injective
      (ordinaryIdeleClassNormSubgroup K) := by
  intro L₁ L₂ h
  apply le_antisymm
  · exact
      (le_iff_ordinaryIdeleClassNormSubgroup_le
        K L₁ L₂).2 h.ge
  · exact
      (le_iff_ordinaryIdeleClassNormSubgroup_le
        K L₂ L₁).2 h.le

/-- The ordinary norm subgroup of a compositum is the intersection of
the two ordinary norm subgroups. -/
theorem ordinaryIdeleClassNormSubgroup_compositum
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L₁ L₂ : FiniteAbelianSubextension K.field) :
    ordinaryIdeleClassNormSubgroup K (L₁.compositum L₂) =
      ordinaryIdeleClassNormSubgroup K L₁ ⊓
        ordinaryIdeleClassNormSubgroup K L₂ := by
  let e :=
    rationalAbstractFixedFieldIdeleClassEquivFixed K.field
  calc
    ordinaryIdeleClassNormSubgroup K (L₁.compositum L₂) =
        ((L₁.compositum L₂).normSubgroup
          rationalIdeleClassRepresentation).map
            e.symm.toAddMonoidHom :=
      ordinaryIdeleClassNormSubgroup_eq_map K (L₁.compositum L₂)
    _ = ((L₁.normSubgroup rationalIdeleClassRepresentation) ⊓
          (L₂.normSubgroup rationalIdeleClassRepresentation)).map
            e.symm.toAddMonoidHom :=
      congrArg
        (fun H => H.map e.symm.toAddMonoidHom)
        (FiniteAbelianSubextension.normSubgroup_compositum
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          K L₁ L₂)
    _ = (L₁.normSubgroup rationalIdeleClassRepresentation).map
          e.symm.toAddMonoidHom ⊓
        (L₂.normSubgroup rationalIdeleClassRepresentation).map
          e.symm.toAddMonoidHom :=
      AddSubgroup.map_inf
        (L₁.normSubgroup rationalIdeleClassRepresentation)
        (L₂.normSubgroup rationalIdeleClassRepresentation)
        e.symm.toAddMonoidHom e.symm.injective
    _ = ordinaryIdeleClassNormSubgroup K L₁ ⊓
        ordinaryIdeleClassNormSubgroup K L₂ :=
      congrArg₂ (fun A B => A ⊓ B)
        (ordinaryIdeleClassNormSubgroup_eq_map K L₁).symm
        (ordinaryIdeleClassNormSubgroup_eq_map K L₂).symm

/-- The ordinary norm subgroup of an intersection field is the product
of the two ordinary norm subgroups. -/
theorem ordinaryIdeleClassNormSubgroup_intersection
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L₁ L₂ : FiniteAbelianSubextension K.field) :
    ordinaryIdeleClassNormSubgroup K (L₁.intersection L₂) =
      ordinaryIdeleClassNormSubgroup K L₁ ⊔
        ordinaryIdeleClassNormSubgroup K L₂ := by
  let e :=
    rationalAbstractFixedFieldIdeleClassEquivFixed K.field
  calc
    ordinaryIdeleClassNormSubgroup K (L₁.intersection L₂) =
        ((L₁.intersection L₂).normSubgroup
          rationalIdeleClassRepresentation).map
            e.symm.toAddMonoidHom :=
      ordinaryIdeleClassNormSubgroup_eq_map K (L₁.intersection L₂)
    _ = ((L₁.normSubgroup rationalIdeleClassRepresentation) ⊔
          (L₂.normSubgroup rationalIdeleClassRepresentation)).map
            e.symm.toAddMonoidHom :=
      congrArg
        (fun H => H.map e.symm.toAddMonoidHom)
        (FiniteAbelianSubextension.normSubgroup_intersection
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          K L₁ L₂)
    _ = (L₁.normSubgroup rationalIdeleClassRepresentation).map
          e.symm.toAddMonoidHom ⊔
        (L₂.normSubgroup rationalIdeleClassRepresentation).map
          e.symm.toAddMonoidHom :=
      AddSubgroup.map_sup
        (L₁.normSubgroup rationalIdeleClassRepresentation)
        (L₂.normSubgroup rationalIdeleClassRepresentation)
        e.symm.toAddMonoidHom
    _ = ordinaryIdeleClassNormSubgroup K L₁ ⊔
        ordinaryIdeleClassNormSubgroup K L₂ :=
      congrArg₂ (fun A B => A ⊔ B)
        (ordinaryIdeleClassNormSubgroup_eq_map K L₁).symm
        (ordinaryIdeleClassNormSubgroup_eq_map K L₂).symm

end GlobalClassFields
end GlobalClassFieldTheory

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassFieldMaximalSubextension
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertTowerRealization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealizationSubextension
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitAbstractFixedField
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.EverywhereUnramifiedTower
public import Nyll.GaloisCohomology.Cyclic.NormKernelVanishing

/-!
# Unramifiedness of the two-stage small Hilbert tower

The second-stage class field is selected in the rational absolute class
formation.  This file transports its exact abstract norm subgroup back
to the ordinary idele class group of the actual middle fixed field.
The intrinsic small-Hilbert characterization then proves genuine
unramifiedness at both finite and infinite places.
-/



@[expose] public section

universe u

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation
open KummerTheory
open LocalClassFieldTheory
open GlobalClassFields

section SelectedTower

variable (K : Type u) [Field K] [NumberField K]

/-- The actual top field in the selected two-stage small Hilbert
tower, viewed over the selected first small Hilbert class field. -/
abbrev smallHilbertTowerTopField :=
  abstractRelativeFixedField ℚ (SeparableClosure ℚ)
    (smallHilbertTowerSecondSubextension K).below

/-- The relative algebra is the canonical algebra carried by the
intermediate-field presentation of the selected top field. -/
@[reducible]
noncomputable def
    smallHilbertTowerTopAlgebra :
    Algebra
      (smallHilbertClassField K)
      (smallHilbertTowerTopField K) :=
  (smallHilbertTowerTopField K).algebra

/-- Freeze the scalar-action owner induced by the canonical relative
algebra. -/
@[reducible]
noncomputable def
    smallHilbertTowerTopSMul :
    SMul
      (smallHilbertClassField K)
      (smallHilbertTowerTopField K) :=
  Algebra.toSMul (self := smallHilbertTowerTopAlgebra K)

/-- Freeze the module owner induced by the same canonical relative
algebra. -/
@[reducible]
noncomputable def
    smallHilbertTowerTopModule :
    Module
      (smallHilbertClassField K)
      (smallHilbertTowerTopField K) :=
  @Algebra.toModule
    (smallHilbertClassField K)
    (smallHilbertTowerTopField K)
    _ _
    (smallHilbertTowerTopAlgebra K)

end SelectedTower

attribute [local instance] smallHilbertTowerTopAlgebra
attribute [local instance] smallHilbertTowerTopSMul
attribute [local instance] smallHilbertTowerTopModule

section SelectedTower

variable (K : Type u) [Field K] [NumberField K]

/-- The second selected stage is finite-dimensional over the first
small Hilbert class field. -/
noncomputable instance smallHilbertTowerTopFiniteDimensional :
    FiniteDimensional
      (smallHilbertClassField K)
      (smallHilbertTowerTopField K) :=
  secondSmallHilbertClassFieldTopFiniteDimensional
    (Reciprocity.numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K))
    (smallHilbertClassFieldSubextension K)

/-- The rational base, first small Hilbert class field, and second
selected stage form the actual scalar tower. -/
noncomputable instance smallHilbertTowerTopScalarTower :
    IsScalarTower ℚ
      (smallHilbertClassField K)
      (smallHilbertTowerTopField K) :=
  secondSmallHilbertClassFieldTopScalarTower
    (Reciprocity.numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K))
    (smallHilbertClassFieldSubextension K)

/-- The selected second stage is a finite extension of the rational
field. -/
noncomputable instance smallHilbertTowerTopAbsoluteFiniteDimensional :
    FiniteDimensional ℚ (smallHilbertTowerTopField K) :=
  secondSmallHilbertClassFieldTopAbsoluteFiniteDimensional
    (Reciprocity.numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K))
    (smallHilbertClassFieldSubextension K)

/-- The selected second-stage fixed field is a number field. -/
noncomputable instance smallHilbertTowerTopNumberField :
    NumberField (smallHilbertTowerTopField K) :=
  secondSmallHilbertClassFieldTopNumberField
    (Reciprocity.numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K))
    (smallHilbertClassFieldSubextension K)

/-- The selected second stage is an abelian Galois extension of the
first small Hilbert class field. -/
noncomputable instance smallHilbertTowerTopIsAbelianGalois :
    IsAbelianGalois
      (smallHilbertClassField K)
      (smallHilbertTowerTopField K) :=
  finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois
    (smallHilbertTowerSecondSubextension K)

end SelectedTower

/-- The actual norm range from the selected second stage is exactly
the intrinsic small-Hilbert subgroup of the first stage. -/
@[simp]
theorem smallHilbertTowerSecondStage_ideleClassNorm_range
    (K : Type u) [Field K] [NumberField K] :
    (_root_.ideleClassNorm
      (smallHilbertClassField K)
      (smallHilbertTowerTopField K)).range =
        smallHilbertClassFieldNormSubgroup
          (K := smallHilbertClassField K) := by
  let K₀ :=
    Reciprocity.numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K)
  let L := smallHilbertClassFieldSubextension K
  let F := abstractFixedField ℚ (SeparableClosure ℚ) L.field
  let T :=
    abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (secondSmallHilbertClassFieldSubextension K₀ L).below
  have hFType : (F : Type) = smallHilbertClassField K := by
    rfl
  have hTType : (T : Type) = (smallHilbertTowerTopField K : Type) := by
    rfl
  cases hFType
  cases hTType
  exact secondSmallHilbertClassFieldSubextension_ideleClassNorm_range K₀ L

/-- The actual second stage in the selected two-stage small Hilbert
tower is everywhere unramified over the first stage. -/
theorem smallHilbertTowerSecondStage_isEverywhereUnramified
    (K : Type u) [Field K] [NumberField K] :
    IsEverywhereUnramified
      (smallHilbertClassField K)
      (smallHilbertTowerTopField K) :=
  isEverywhereUnramified_of_normRange_eq_smallHilbertNormSubgroup
    (smallHilbertTowerSecondStage_ideleClassNorm_range K)

/-- In the selected two-stage small Hilbert tower, the maximal abelian
intermediate extension of the top over the original base is exactly
the first small Hilbert class field. -/
theorem smallHilbertTower_maximalAbelianSubextension_eq_firstStage
    (K : Type u) [Field K] [NumberField K] :
    maximalAbelianSubextension
        (smallHilbertTowerGaloisRealization K) =
      smallHilbertClassFieldSubextension K := by
  classical
  let K₀ :=
    Reciprocity.numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K)
  let L := smallHilbertClassFieldSubextension K
  let M := smallHilbertTowerSecondSubextension K
  let P := smallHilbertTowerGaloisRealization K
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) K₀.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below
  let T :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K₀.field (le_baseField K₀.field)) :=
    K₀.finite
  let hLfinite : Finite
      (K₀.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          K₀.field L.field L.below) :=
    L.finite
  let hPfinite : Finite
      (K₀.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          K₀.field P.field P.below) :=
    P.finite
  let : NumberField F := by
    let : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K₀.field hKfinite
    exact NumberField.of_module_finite ℚ F
  let : NumberField E := by
    let : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ)
        K₀.field L.field L.below hKfinite hLfinite
    exact NumberField.of_module_finite F E
  let : NumberField T := by
    let : FiniteDimensional F T :=
      abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ)
        K₀.field P.field P.below hKfinite hPfinite
    exact NumberField.of_module_finite F T
  have hPM : P.field = M.field := by
    simp only [
      P, smallHilbertTowerGaloisRealization,
      smallHilbertClassFieldGaloisSubextension,
      galoisSubextensionOfConjugateStableAbelianTower_field,
      M]
  have hPL : P.field.toSubgroup ≤ L.field.toSubgroup := by
    rw [hPM]
    exact M.below
  have hET : E ≤ T := by
    intro x hx
    change x ∈ abstractFixedField ℚ (SeparableClosure ℚ) L.field at hx
    change x ∈ abstractFixedField ℚ (SeparableClosure ℚ) P.field
    exact
      (abstractFixedField_le ℚ (SeparableClosure ℚ) hPL) hx
  let hETAlgebra : Algebra E T :=
    (IntermediateField.inclusion hET).toRingHom.toAlgebra
  let hFETScalarTower :
      @IsScalarTower F E T
        (Algebra.toSMul (R := F) (A := E))
        hETAlgebra.toSMul
        (Algebra.toSMul (R := F) (A := T)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hFirst :
      IsEverywhereUnramified F E := by
    apply
      isEverywhereUnramified_of_normRange_eq_smallHilbertNormSubgroup
        (K := F) (L := E)
    simpa only [F, E, K₀, L] using
      (smallHilbertClassField_ideleClassNorm_range_eq_intrinsic
        (K := K))
  have hEType : (E : Type) = smallHilbertClassField K := by
    rfl
  have hTType : (T : Type) = (smallHilbertTowerTopField K : Type) := by
    change
      (abstractFixedField ℚ (SeparableClosure ℚ) P.field : Type) =
        (abstractFixedField ℚ (SeparableClosure ℚ) M.field : Type)
    rw [hPM]
  have hSecond :
      IsEverywhereUnramified E T := by
    cases hEType
    cases hTType
    exact smallHilbertTowerSecondStage_isEverywhereUnramified K
  have hunramifiedTop :
      IsEverywhereUnramified F T :=
    IsEverywhereUnramified.trans hFirst hSecond
  apply le_antisymm
  · exact
      maximalAbelianSubextension_le_smallHilbertClassField_of_everywhereUnramified
        K₀ L P
        (GlobalClassFields.smallHilbertClassFieldSubextension_normSubgroup
          (K := K))
        hunramifiedTop
  · exact
      smallHilbertTowerBase_le_maximalAbelianSubextension
        K₀ L M
        ((smallHilbertTowerSecondSubextension_normSubgroup K).trans
          (smallHilbertTowerMiddleNormSubgroup_eq_conjugationEndpoint K₀ L))

end IdealClassFieldTheory
end GlobalClassFieldTheory

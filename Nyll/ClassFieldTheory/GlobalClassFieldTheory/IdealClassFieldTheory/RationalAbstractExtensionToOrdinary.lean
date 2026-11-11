/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.AbstractCapitulation
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Tower
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassGroup
public import Nyll.GaloisCohomology.Kummer.Abstract.KummerDelta

/-!
# Rational abstract extension transport to ordinary idele classes

Compatibility of abstract extension with ordinary idele classes.
-/



@[expose] public section

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation
open CyclicCohomology

section RationalIdeleExtension

open Reciprocity
open LocalClassFieldTheory

attribute [local instance]
  rationalAbstractFixedFieldFiniteDimensional rationalIdeleClassDirectLimitSMul
  rationalAbstractTowerClassGroupCommGroup

/-- The abstract extension representation, followed by the actual
relative-to-ordinary comparison over the intermediate fixed field, is
the direct ordinary idele class represented by its upper fixed part. -/
theorem rationalAbstractExtensionIdeleClassEquiv_to_ordinary
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (x : (extensionFixedRepresentation
      rationalIdeleClassRepresentation
      K L hLK hnormal).V) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
    let _ : (extensionSubgroup K L hLK).Normal := hnormal
    let _ : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K hKfinite
    let _ : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
    let _ : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    let _ : FiniteDimensional ℚ E :=
      FiniteDimensional.trans ℚ F E
    let _ : FiniteDimensional ℚ (E.restrictScalars ℚ) := by
      change FiniteDimensional ℚ
        (abstractFixedField ℚ (SeparableClosure ℚ) L)
      change FiniteDimensional ℚ E
      infer_instance
    let _ : NumberField F :=
      NumberField.of_module_finite ℚ F
    let _ : NumberField E :=
      NumberField.of_module_finite ℚ E
    (MulEquiv.toAdditive
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := F) (L := E)))
        (rationalAbstractExtensionIdeleClassEquiv
          K L hLK hnormal x) =
      (rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
        K L hLK).symm
        (extensionFixedRepresentationEquiv
          rationalIdeleClassRepresentation
          K L hLK hnormal x) := by
  intro F E hnormalInstance hFfinite hFEfinite htower hEfinite
    hRestrictFinite hFnumberField hEnumberField
  let eAmbient :=
    extensionFixedRepresentationEquiv
      rationalIdeleClassRepresentation K L hLK hnormal
  let eFixed :
      Additive (IdeleClassGroup E) ≃+
        KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation L :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
      K L hLK
  let eRelative :
      Additive (RelativeIdeleGroup.ClassGroup ℚ E) ≃+
        Additive (IdeleClassGroup E) :=
    MulEquiv.toAdditive
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := E))
  let eTower :
      Additive (RelativeIdeleGroup.ClassGroup ℚ E) ≃+
        Additive (RelativeIdeleGroup.ClassGroup F E) :=
    (MulEquiv.toAdditive
      (TowerRelativeIdeleGroup.classGroupEquiv
        ℚ F E).symm).trans
      (MulEquiv.toAdditive
        (towerRelativeIdeleClassBaseChangeMulEquiv
          ℚ F E))
  let c :
      Additive (RelativeIdeleGroup.ClassGroup ℚ E) :=
    eRelative.symm (eFixed.symm (eAmbient x))
  have htransport :
      (MulEquiv.toAdditive
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := F) (L := E))) (eTower c) =
        eRelative c := by
    change
      Additive.ofMul
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := F) (L := E)
            (towerRelativeIdeleClassBaseChangeMulEquiv ℚ F E
              ((TowerRelativeIdeleGroup.classGroupEquiv
                ℚ F E).symm (Additive.toMul c)))) =
        Additive.ofMul
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := E) (Additive.toMul c))
    exact
      congrArg Additive.ofMul
        (relativeIdeleClassBaseChangeMulEquiv_tower
          ℚ F E (Additive.toMul c))
  change
    (MulEquiv.toAdditive
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := F) (L := E)))
        (eTower
          (eRelative.symm
            (eFixed.symm (eAmbient x)))) =
      eFixed.symm (eAmbient x)
  calc
    _ = eRelative c := htransport
    _ = eFixed.symm (eAmbient x) := by
      exact eRelative.apply_symm_apply
        (eFixed.symm (eAmbient x))

end RationalIdeleExtension

end IdealClassFieldTheory
end GlobalClassFieldTheory

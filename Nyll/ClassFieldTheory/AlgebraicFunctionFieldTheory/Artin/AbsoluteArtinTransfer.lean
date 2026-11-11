/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.NativeTransferCoordinates
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.NormalAbelianSeparation
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve

/-!
# Native absolute Artin and original transfer

The actual finite Artin inclusion formula and the actual finite
coordinates of topological transfer give the absolute inclusion square
at every relative abelian fixed field which is normal over the original
base. Cofinality of these actual finite stages then proves the full
absolute inclusion square. Its Galois arrow is the original group-theoretic
transfer.
-/

@[expose] public section

universe u v

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory ProCGroups.Abelian
open ProCGroups.FiniteStepSolvableQuotients
open scoped IsMulCommutative

-- These maps are compared by their projection and abelianization formulas.
attribute [local irreducible] abelianFiniteArtin finiteArtin

variable (k : Type u) (K : Type v) [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [AlgebraicCurve.HasPrincipalDivisors k K]

/-- Original absolute transfer agrees with native reciprocity of actual
idele-class inclusion at every actual relative abelian fixed-field
coordinate normal over the original field. -/
theorem absoluteArtin_transfer_fixedFieldCoordinate
    (H : FiniteAbstractField Gal(SeparableClosure K/K)) [H.field.toSubgroup.Normal]
    (T : FiniteGaloisSubextension H.field)
    [T.field.toSubgroup.Normal] [IsMulCommutative T.extensionQuotient] :
    let F := abstractFixedField K (SeparableClosure K) H.field
    let _ : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).toSubalgebra.algebra
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    have _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    have _ : FiniteDimensional K (abstractFixedField K (SeparableClosure K) H.field) :=
      abstractFixedField_finiteDimensional K (SeparableClosure K) H.field H.finite
    have _ : Finite (Gal(SeparableClosure K/K) ⧸ H.field.toSubgroup) :=
      ambientQuotientFiniteOfAbstractFinite K (SeparableClosure K) H.field H.finite
    ∀ c : IdeleClassGroup k K,
      fixedFieldFiniteArtinProjection K (SeparableClosure K) H T
          (fixedFieldAbsoluteArtinOfClosure k K (SeparableClosure K) H e
            (IdeleClassGroup.baseChange (k := k) (K := K)
              (L := abstractFixedField K (SeparableClosure K) H.field) c)) =
        fixedFieldFiniteArtinProjection K (SeparableClosure K) H T
          (openNormalTransferTopologicalAbelianization
            (finiteAbstractOpenNormal K (SeparableClosure K) H) (absoluteArtin k K c)) := by
  intro F aFsep e akΩ aRΩ hkKΩ hRKΩ hkRΩ hKF hHfinite c
  let Ω := SeparableClosure K
  let E := abstractFixedField K Ω T.field
  let _ : CommSemiring E := (inferInstance : Field E).toSemifield |>.toCommSemiring
  let aKE : Algebra K E := IntermediateField.algebra' (R' := K) E
  let _ : SMul K E := aKE.toSMul
  let _ : Algebra k E := IntermediateField.algebra' (R' := k) E
  let aFE : Algebra F E := (abstractRelativeFixedField K Ω T.below).algebra
  let _ : SMul F E := aFE.toSMul
  let _ : Module F E := aFE.toModule
  have hkFΩ : IsScalarTower k F Ω := IsScalarTower.to₁₃₄ k K F Ω
  have hRFΩ : IsScalarTower (RatFunc k) F Ω := IsScalarTower.to₁₃₄ (RatFunc k) K F Ω
  have hKFE : IsScalarTower K F E :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hKE : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional K Ω T.field T.toFiniteAbstractFieldExtension.field.finite
  have hKEgal : IsGalois K E := IsGalois.of_fixedField_normal_subgroup T.field.toSubgroup
  have hkFE : IsScalarTower k F E :=
    IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext
      (IsScalarTower.algebraMap_apply k F Ω x))
  have hFE : FiniteDimensional F E := FiniteDimensional.right K F E
  have hFEgal : IsGalois F E := IsGalois.tower_top_of_isGalois K F E
  have hFprincipal : AlgebraicCurve.HasPrincipalDivisors k F :=
    (isCurveOver k F).toHasPrincipalDivisors
  have hEprincipal : AlgebraicCurve.HasPrincipalDivisors k E :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K E).toHasPrincipalDivisors
  have hab : IsAbelianGalois F E :=
    fixedFieldRelative_isAbelianGalois K Ω H T
  let cF : IdeleClassGroup k F :=
    IdeleClassGroup.baseChange (k := k) (K := K) (L := F) c
  have hleft := fixedFieldAbsoluteArtinOfClosure_projection k K Ω H T e cF
  have hleftAb :=
    congrArg (Abelianization.of : Gal(E/F) → Abelianization Gal(E/F)) hleft
  have habel := abelianFiniteArtin_of k F E cF
  have hfinite := finiteArtin_baseChange_transfer_of_fixedField k K H T c
  have hright :=
    (nativeFixedFieldAbelianizedTransfer_absoluteCoordinate K H T (absoluteArtin k K c)).trans
      (congrArg (nativeFixedFieldAbelianizedTransfer K H T)
        (absoluteArtin_abelianizedRestriction k K E c))
  exact (Abelianization.equivOfComm (H := Gal(E/F))).injective
    (hleftAb.trans (habel.trans (hfinite.trans hright.symm)))

/-- Native absolute reciprocity carries original idele-class inclusion
to the original topological transfer into the actual finite fixed subgroup.
All finite coordinates have been compared, and their joint separation
proves equality in the full topological abelianization. -/
theorem absoluteArtin_baseChange_originalTransfer
    (H : FiniteAbstractField Gal(SeparableClosure K/K)) [H.field.toSubgroup.Normal] :
    let F := abstractFixedField K (SeparableClosure K) H.field
    let _ : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).toSubalgebra.algebra
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    have _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    have _ : FiniteDimensional K (abstractFixedField K (SeparableClosure K) H.field) :=
      abstractFixedField_finiteDimensional K (SeparableClosure K) H.field H.finite
    have _ : Finite (Gal(SeparableClosure K/K) ⧸ H.field.toSubgroup) :=
      ambientQuotientFiniteOfAbstractFinite K (SeparableClosure K) H.field H.finite
    ∀ c : IdeleClassGroup k K,
      fixedFieldAbsoluteArtinOfClosure k K (SeparableClosure K) H e
          (IdeleClassGroup.baseChange (k := k) (K := K)
            (L := abstractFixedField K (SeparableClosure K) H.field) c) =
        openNormalTransferTopologicalAbelianization
          (finiteAbstractOpenNormal K (SeparableClosure K) H) (absoluteArtin k K c) := by
  intro F aFsep e akΩ aRΩ hkKΩ hRKΩ hkRΩ hKF hHfinite c
  apply fixedFieldFiniteArtinProjection_ext K (SeparableClosure K) H
  intro T hTnormal hTcomm
  exact absoluteArtin_transfer_fixedFieldCoordinate k K H T e c

/-- The original group transfer expressed between the two native absolute
abelian Galois groups, using only the actual separable-closure equivalence. -/
def nativeAbsoluteTransferOfFixedField
    (H : FiniteAbstractField Gal(SeparableClosure K/K)) [H.field.toSubgroup.Normal] :
    let F := abstractFixedField K (SeparableClosure K) H.field
    let _ : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).toSubalgebra.algebra
    ∀ _ : SeparableClosure F ≃ₐ[F] SeparableClosure K,
    localAbsoluteAbelianProfinite K →ₜ*
      localAbsoluteAbelianProfinite (abstractFixedField K (SeparableClosure K) H.field) := by
  intro F aFsep e
  have hHfinite : Finite (Gal(SeparableClosure K/K) ⧸ H.field.toSubgroup) :=
    ambientQuotientFiniteOfAbstractFinite K (SeparableClosure K) H.field H.finite
  exact (ContinuousMonoidHom.toContinuousMonoidHom
    (fixedFieldAbsoluteAbelianEquivOfClosure K (SeparableClosure K) H e).symm).comp
      (openNormalTransferTopologicalAbelianization
        (finiteAbstractOpenNormal K (SeparableClosure K) H))

/-- In native absolute Galois coordinates, actual finite Galois
base-change of idele classes is the original transfer. -/
theorem absoluteArtin_baseChange_nativeTransfer
    (H : FiniteAbstractField Gal(SeparableClosure K/K)) [H.field.toSubgroup.Normal] :
    let F := abstractFixedField K (SeparableClosure K) H.field
    let _ : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).toSubalgebra.algebra
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    have _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    have _ : FiniteDimensional K (abstractFixedField K (SeparableClosure K) H.field) :=
      abstractFixedField_finiteDimensional K (SeparableClosure K) H.field H.finite
    ∀ c : IdeleClassGroup k K,
      absoluteArtin k (abstractFixedField K (SeparableClosure K) H.field)
          (IdeleClassGroup.baseChange (k := k) (K := K)
            (L := abstractFixedField K (SeparableClosure K) H.field) c) =
        nativeAbsoluteTransferOfFixedField K H e (absoluteArtin k K c) := by
  intro F aFsep e akΩ aRΩ hkKΩ hRKΩ hkRΩ hKF c
  have hHfinite : Finite (Gal(SeparableClosure K/K) ⧸ H.field.toSubgroup) :=
    ambientQuotientFiniteOfAbstractFinite K (SeparableClosure K) H.field H.finite
  apply (fixedFieldAbsoluteAbelianEquivOfClosure K (SeparableClosure K) H e).injective
  change fixedFieldAbsoluteArtinOfClosure k K (SeparableClosure K) H e
      (IdeleClassGroup.baseChange (k := k) (K := K)
        (L := abstractFixedField K (SeparableClosure K) H.field) c) =
    fixedFieldAbsoluteAbelianEquivOfClosure K (SeparableClosure K) H e
      ((fixedFieldAbsoluteAbelianEquivOfClosure K (SeparableClosure K) H e).symm
        (openNormalTransferTopologicalAbelianization
          (finiteAbstractOpenNormal K (SeparableClosure K) H) (absoluteArtin k K c)))
  rw [ContinuousMulEquiv.apply_symm_apply]
  exact absoluteArtin_baseChange_originalTransfer k K H e c

end FunctionField

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.FieldTheory.Galois.Abelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.EmbeddedFixedFieldTower
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteAbelian
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.NativeFixedFieldNormCompatibility
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm
import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup

/-!
# Norm reciprocity for actual finite intermediate fields

The fixed-field representation transfers the proved native norm formula to
the original embedded tower, with its actual inclusion and scalar action.
-/

noncomputable section
open ClassFormation LocalClassFieldTheory CyclicCohomology RamificationTheory
open scoped IsMulCommutative

namespace FunctionField

private theorem fixedFieldQuotient_isMulCommutative
    (K : Type) [Field K]
    (H : FiniteAbstractField Gal(SeparableClosure K/K))
    (T : FiniteGaloisSubextension H.field)
    [IsAbelianGalois K (abstractFixedField K (SeparableClosure K) T.field)] :
    IsMulCommutative T.extensionQuotient := by
  let F := abstractFixedField K (SeparableClosure K) H.field
  let E := abstractFixedField K (SeparableClosure K) T.field
  let aFE : Algebra F E := (abstractRelativeFixedField K (SeparableClosure K) T.below).algebra
  let sFE : SMul F E := aFE.toSMul
  let mFE : Module F E := aFE.toModule
  have hKFE : IsScalarTower K F E :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hFEabelian : IsAbelianGalois F E := IsAbelianGalois.tower_top K F E
  let eG : T.extensionQuotient ≃* Gal(E/F) :=
    abstractExtensionQuotientEquivGaloisGroup K (SeparableClosure K)
      H.field T.field T.below T.normal
  apply IsMulCommutative.of_comm
  intro x y
  apply eG.injective
  rw [map_mul, map_mul, mul_comm]

variable (k K : Type) [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [AlgebraicCurve.HasPrincipalDivisors k K]
    [Algebra k (SeparableClosure K)] [Algebra (RatFunc k) (SeparableClosure K)]
    [IsScalarTower k K (SeparableClosure K)]
    [IsScalarTower (RatFunc k) K (SeparableClosure K)]
    [IsScalarTower k (RatFunc k) (SeparableClosure K)]

private theorem abelianFiniteArtin_norm_restrictScalars_fixedField
    (H : FiniteAbstractField Gal(SeparableClosure K/K))
    (T : FiniteGaloisSubextension H.field)
    [H.field.toSubgroup.Normal] [T.field.toSubgroup.Normal]
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) H.field)]
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) T.field)]
    [IsGalois K (abstractFixedField K (SeparableClosure K) H.field)]
    [IsAbelianGalois K (abstractFixedField K (SeparableClosure K) T.field)]
    [Algebra (RatFunc k) (abstractFixedField K (SeparableClosure K) H.field)]
    [IsScalarTower k (RatFunc k) (abstractFixedField K (SeparableClosure K) H.field)]
    [FunctionField k (abstractFixedField K (SeparableClosure K) H.field)]
    [AlgebraicCurve.HasPrincipalDivisors k (abstractFixedField K (SeparableClosure K) H.field)]
    [AlgebraicCurve.HasPrincipalDivisors k (abstractFixedField K (SeparableClosure K) T.field)] :
    let aFE : Algebra (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) :=
      (IntermediateField.inclusion
        (abstractFixedField_le K (SeparableClosure K) T.below)).toRingHom.toAlgebra
    let _ : SMul (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) := aFE.toSMul
    let _ : Module (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) := aFE.toModule
    let _ : IsScalarTower K (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : IsScalarTower k (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : FiniteDimensional (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) :=
      FiniteDimensional.right K (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field)
    let _ : IsAbelianGalois (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) :=
      IsAbelianGalois.tower_top K (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field)
    ∀ c : IdeleClassGroup k (abstractFixedField K (SeparableClosure K) H.field),
      abelianFiniteArtin k K (abstractFixedField K (SeparableClosure K) T.field)
          (IdeleClassGroup.norm (k := k) (K := K)
            (L := abstractFixedField K (SeparableClosure K) H.field) c) =
        AlgEquiv.restrictScalarsHom K
          (abelianFiniteArtin k (abstractFixedField K (SeparableClosure K) H.field)
            (abstractFixedField K (SeparableClosure K) T.field) c) := by
  intro aFE sFE mFE hKFE hkFE hFEfinite hFEabelian c
  have hcomm : IsMulCommutative T.extensionQuotient :=
    fixedFieldQuotient_isMulCommutative K H T
  apply (Abelianization.equivOfComm
    (H := Gal((abstractFixedField K (SeparableClosure K) T.field)/K))).injective
  change Abelianization.of
      (abelianFiniteArtin k K (abstractFixedField K (SeparableClosure K) T.field)
        (IdeleClassGroup.norm
          (k := k) (K := K) (L := abstractFixedField K (SeparableClosure K) H.field) c)) =
    Abelianization.of (AlgEquiv.restrictScalarsHom K
      (abelianFiniteArtin k (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) c))
  let r : Gal((abstractFixedField K (SeparableClosure K) T.field)/
      (abstractFixedField K (SeparableClosure K) H.field)) →*
      Gal((abstractFixedField K (SeparableClosure K) T.field)/K) :=
    AlgEquiv.restrictScalarsHom K
  have hLower := abelianFiniteArtin_of k K
    (abstractFixedField K (SeparableClosure K) T.field)
    (IdeleClassGroup.norm (k := k) (K := K)
      (L := abstractFixedField K (SeparableClosure K) H.field) c)
  have hUpper := abelianFiniteArtin_of k
    (abstractFixedField K (SeparableClosure K) H.field)
    (abstractFixedField K (SeparableClosure K) T.field) c
  have hNorm := finiteArtin_norm_restrictScalars_of_fixedField k K H T c
  have hMap := Abelianization.map_of r
    (abelianFiniteArtin k (abstractFixedField K (SeparableClosure K) H.field)
      (abstractFixedField K (SeparableClosure K) T.field) c)
  exact hLower.trans (hNorm.trans ((congrArg (Abelianization.map r) hUpper).symm.trans hMap))

variable
    (F E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K F] [FiniteDimensional K E]
    [IsGalois K F] [IsAbelianGalois K E]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    [AlgebraicCurve.HasPrincipalDivisors k F] [AlgebraicCurve.HasPrincipalDivisors k E]

/-- For actual finite intermediate fields, the native Artin value of a class
norm is the upper Artin automorphism with its scalars restricted. -/
theorem abelianFiniteArtin_norm_restrictScalars (hFE : F ≤ E) :
    let aFE : Algebra F E := (IntermediateField.inclusion hFE).toRingHom.toAlgebra
    let _ : SMul F E := aFE.toSMul
    let _ : Module F E := aFE.toModule
    let _ : IsScalarTower K F E :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : IsScalarTower k F E :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : FiniteDimensional F E := FiniteDimensional.right K F E
    let _ : IsAbelianGalois F E := IsAbelianGalois.tower_top K F E
    ∀ c : IdeleClassGroup k F,
      abelianFiniteArtin k K E
          (IdeleClassGroup.norm (k := k) (K := K) (L := F) c) =
        AlgEquiv.restrictScalarsHom K (abelianFiniteArtin k F E c) := by
  obtain ⟨H, T, hF, hE, hHnormal, hTnormal⟩ :=
    exists_embeddedFixedFieldTower K F E hFE
  subst F
  subst E
  exact abelianFiniteArtin_norm_restrictScalars_fixedField k K H T

end FunctionField

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldArtinTransfer
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.NativePresentation
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldBaseCompatibility
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTower
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.ClassFieldTheory.Algebra.GaloisRestrictionFinrankOne

/-!
# Native Artin inclusion and the original finite transfer

The intrinsic abstract base has actual degree one over the original field.
Its Galois-group comparison is therefore the original scalar restriction.
Transporting the proved fixed-field transfer through this comparison gives
a map on native Galois abelianizations, independently of reciprocity.

For an actual finite fixed base and an abelian extension above it which is
normal over the original field, native Artin symbols commute with actual
idele-class inclusion and this original group transfer. The Galois group
over the original field need not be abelian.
-/

@[expose] public section

universe u v w

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

/-- An actual finite abstract field, viewed over the intrinsic degree-one base. -/
@[reducible] def finiteAbstractFieldOverIntrinsicBase
    (K : Type v) [Field K]
    (H : FiniteAbstractField Gal(SeparableClosure K/K)) :
    FiniteAbstractFieldExtension Gal(SeparableClosure K/K) := by
  have hB : (intrinsicFiniteAbstractBase K).field =
      baseField Gal(SeparableClosure K/K) :=
    congrArg FiniteAbstractField.field (intrinsicFiniteAbstractBase_eq_base K)
  have hHB : H.field.toSubgroup ≤ (intrinsicFiniteAbstractBase K).field.toSubgroup := by
    rw [hB]
    exact le_baseField H.field
  exact
    { field := H
      base := intrinsicFiniteAbstractBase K
      below := hHB
      finiteQuotient :=
        (congrArg (fun V : ClosedSubgroup Gal(SeparableClosure K/K) =>
          Finite (V.toSubgroup ⧸ H.field.toSubgroup.subgroupOf V.toSubgroup)) hB).mpr
          H.finite }

section NativeTransfer

variable (K : Type v) [Field K]
    (H : FiniteAbstractField Gal(SeparableClosure K/K))
    (T : FiniteGaloisSubextension H.field) [T.field.toSubgroup.Normal]

/-- Finite group transfer on the native relative Galois groups. The source
is identified with the intrinsic-base presentation only by degree-one
scalar restriction, without using an Artin symbol. -/
def nativeFixedFieldAbelianizedTransfer :
    Abelianization Gal((abstractFixedField K (SeparableClosure K) T.field)/K) →*
      Abelianization Gal((abstractRelativeFixedField K (SeparableClosure K) T.below)/
        (abstractFixedField K (SeparableClosure K) H.field)) := by
  let S := finiteAbstractFieldOverIntrinsicBase K H
  let F₀ := abstractFixedField K (SeparableClosure K) (intrinsicFiniteAbstractBase K).field
  let E := abstractFixedField K (SeparableClosure K) T.field
  have hTB : T.field.toSubgroup ≤ S.base.field.toSubgroup := T.below.trans S.below
  have hTnormal : (extensionSubgroup S.base.field T.field hTB).Normal := by
    infer_instance
  have hTfinite : Finite
      (S.base.field.toSubgroup ⧸ extensionSubgroup S.base.field T.field hTB) :=
    (finiteAbstractFieldOverIntrinsicBase K T.toFiniteAbstractFieldExtension.field).finiteQuotient
  let aF₀E : Algebra F₀ E := (abstractRelativeFixedField K (SeparableClosure K) hTB).algebra
  have hKF₀E : IsScalarTower K F₀ E :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hF₀ : Module.finrank K F₀ = 1 := by
    rw [← (finiteGaloisBaseFixedFieldEquiv K).toLinearEquiv.finrank_eq,
      Module.finrank_self]
  let e₀ : Gal(E/F₀) ≃* Gal(E/K) :=
    ClassFieldTheory.galoisRestrictScalarsEquivOfFinrankOne hF₀
  exact (fixedFieldAbelianizedTransfer K (SeparableClosure K) S T.field T.below).comp
    e₀.abelianizationCongr.symm.toMonoidHom

private theorem nativeFixedFieldAbelianizedTransfer_intrinsic :
    let S := finiteAbstractFieldOverIntrinsicBase K H
    let F₀ := abstractFixedField K (SeparableClosure K) (intrinsicFiniteAbstractBase K).field
    let E := abstractFixedField K (SeparableClosure K) T.field
    have hTB : T.field.toSubgroup ≤ S.base.field.toSubgroup := T.below.trans S.below
    have hTnormal : (extensionSubgroup S.base.field T.field hTB).Normal := inferInstance
    have hTfinite : Finite
        (S.base.field.toSubgroup ⧸ extensionSubgroup S.base.field T.field hTB) :=
      (finiteAbstractFieldOverIntrinsicBase K T.toFiniteAbstractFieldExtension.field).finiteQuotient
    let _ : Algebra F₀ E := (abstractRelativeFixedField K (SeparableClosure K) hTB).algebra
    have _ : IsScalarTower K F₀ E :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    have hF₀ : Module.finrank K F₀ = 1 := by
      rw [← (finiteGaloisBaseFixedFieldEquiv K).toLinearEquiv.finrank_eq,
        Module.finrank_self]
    let e₀ : Gal(E/F₀) ≃* Gal(E/K) :=
      ClassFieldTheory.galoisRestrictScalarsEquivOfFinrankOne hF₀
    ∀ b : Abelianization Gal(E/F₀),
      nativeFixedFieldAbelianizedTransfer K H T (e₀.abelianizationCongr b) =
        fixedFieldAbelianizedTransfer K (SeparableClosure K) S T.field T.below b := by
  intro S F₀ E hTB hTnormal hTfinite aF₀E hKF₀E hF₀ e₀ b
  exact congrArg (fixedFieldAbelianizedTransfer K (SeparableClosure K) S T.field T.below)
    (e₀.abelianizationCongr.symm_apply_apply b)

end NativeTransfer

section NativeArtin

variable (k : Type u) (K : Type v) [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [AlgebraicCurve.HasPrincipalDivisors k K]
    [Algebra k (SeparableClosure K)] [Algebra (RatFunc k) (SeparableClosure K)]
    [IsScalarTower k K (SeparableClosure K)]
    [IsScalarTower (RatFunc k) K (SeparableClosure K)]
    [IsScalarTower k (RatFunc k) (SeparableClosure K)]

private theorem finiteArtin_intrinsicBase_equiv
    (S : ClosedSubgroup Gal(SeparableClosure K/K))
    (hSB : S.toSubgroup ≤ (intrinsicFiniteAbstractBase K).field.toSubgroup)
    [hSnormal : (extensionSubgroup (intrinsicFiniteAbstractBase K).field S hSB).Normal]
    [hSfinite : Finite ((intrinsicFiniteAbstractBase K).field.toSubgroup ⧸
      extensionSubgroup (intrinsicFiniteAbstractBase K).field S hSB)]
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) S)]
    [IsGalois K (abstractFixedField K (SeparableClosure K) S)]
    [AlgebraicCurve.HasPrincipalDivisors k (abstractFixedField K (SeparableClosure K) S)] :
    let F₀ := abstractFixedField K (SeparableClosure K) (intrinsicFiniteAbstractBase K).field
    let E := abstractFixedField K (SeparableClosure K) S
    let aF₀E : Algebra F₀ E := (abstractRelativeFixedField K (SeparableClosure K) hSB).algebra
    let _ : SMul F₀ E := aF₀E.toSMul
    have _ : IsScalarTower K F₀ E :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    have _ : FiniteDimensional K F₀ :=
      (finiteGaloisBaseFixedFieldEquiv K).toLinearEquiv.finiteDimensional
    have hF₀ : Module.finrank K F₀ = 1 := by
      rw [← (finiteGaloisBaseFixedFieldEquiv K).toLinearEquiv.finrank_eq,
        Module.finrank_self]
    ∀ c : IdeleClassGroup k K,
      finiteArtin k K E c =
        (ClassFieldTheory.galoisRestrictScalarsEquivOfFinrankOne
          (E := E) hF₀).abelianizationCongr
          (fixedFieldArtin k K (SeparableClosure K) (intrinsicFiniteAbstractBase K)
            ⟨S, hSB, hSnormal, hSfinite⟩
            (IdeleClassGroup.baseChange (k := k) (K := K) (L := F₀) c)) := by
  intro F₀ E aF₀E sF₀E hKF₀E hKF₀ hF₀ c
  let e₀ : Gal(E/F₀) ≃* Gal(E/K) :=
    ClassFieldTheory.galoisRestrictScalarsEquivOfFinrankOne hF₀
  let r : Gal(E/F₀) →* Gal(E/K) := AlgEquiv.restrictScalarsHom K
  have he₀ (z : Abelianization Gal(E/F₀)) :
      e₀.abelianizationCongr z = Abelianization.map r z := by
    refine QuotientGroup.induction_on z ?_
    intro σ
    change Abelianization.of (e₀ σ) = Abelianization.of (σ.restrictScalars K)
    rfl
  exact (finiteArtin_eq_intrinsicFixedField_restrict k K S hSB c).trans (he₀ _).symm

omit [Algebra k (SeparableClosure K)] [Algebra (RatFunc k) (SeparableClosure K)]
  [IsScalarTower k K (SeparableClosure K)]
  [IsScalarTower (RatFunc k) K (SeparableClosure K)]
  [IsScalarTower k (RatFunc k) (SeparableClosure K)] in
private theorem fixedFieldArtin_baseChange_originalTransfer
    (Ω : Type w) [Field Ω] [Algebra K Ω] [Algebra k Ω]
    [Algebra (RatFunc k) Ω] [IsScalarTower k K Ω]
    [IsScalarTower (RatFunc k) K Ω] [IsScalarTower k (RatFunc k) Ω]
    [IsGalois K Ω] [IsSepClosed Ω]
    (S : FiniteAbstractFieldExtension Gal(Ω/K))
    (T : FiniteGaloisSubextension S.field.field)
    [hTnormal : (extensionSubgroup S.base.field T.field (T.below.trans S.below)).Normal]
    [hTfinite : Finite (S.base.field.toSubgroup ⧸
      extensionSubgroup S.base.field T.field (T.below.trans S.below))] :
    let F₀ := abstractFixedField K Ω S.base.field
    let F := abstractFixedField K Ω S.field.field
    let U : FiniteGaloisSubextension S.base.field :=
      ⟨T.field, T.below.trans S.below, hTnormal, hTfinite⟩
    have _ : FiniteDimensional K F₀ :=
      abstractFixedField_finiteDimensional K Ω S.base.field S.base.finite
    have _ : FiniteDimensional K F :=
      abstractFixedField_finiteDimensional K Ω S.field.field S.field.finite
    let _ : Algebra F₀ F :=
      (IntermediateField.inclusion
        (abstractFixedField_le K Ω S.below)).toRingHom.toAlgebra
    have _ : IsScalarTower K F₀ F :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    have _ : IsScalarTower k F₀ F :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    have _ : FiniteDimensional F₀ F := FiniteDimensional.right K F₀ F
    have _ : Algebra.IsSeparable F₀ F :=
      Algebra.isSeparable_tower_top_of_isSeparable K F₀ F
    ∀ c : IdeleClassGroup k K,
      fixedFieldArtin k K Ω S.field T
          (IdeleClassGroup.baseChange (k := k) (K := K) (L := F) c) =
        fixedFieldAbelianizedTransfer K Ω S T.field T.below
          (fixedFieldArtin k K Ω S.base U
            (IdeleClassGroup.baseChange (k := k) (K := K) (L := F₀) c)) := by
  intro F₀ F U hKF₀ hKF aF₀F hKF₀F hkF₀F hF₀F hF₀Fsep c
  let c₀ := IdeleClassGroup.baseChange (k := k) (K := K) (L := F₀) c
  have hTower : IdeleClassGroup.baseChange (k := k) (K := F₀) (L := F) c₀ =
      IdeleClassGroup.baseChange (k := k) (K := K) (L := F) c :=
    IdeleClassGroup.baseChange_trans (k := k) (K := K) (L := F₀) (M := F) c
  exact (congrArg (fixedFieldArtin k K Ω S.field T) hTower.symm).trans
    (fixedFieldArtin_baseChange_transfer k K Ω S T.field T.below c₀)

omit [Algebra k (SeparableClosure K)] [Algebra (RatFunc k) (SeparableClosure K)]
  [IsScalarTower k K (SeparableClosure K)]
  [IsScalarTower (RatFunc k) K (SeparableClosure K)]
  [IsScalarTower k (RatFunc k) (SeparableClosure K)] in
private theorem fixedFieldArtin_baseChange_nativeTransfer :
    let _ : CommSemiring (SeparableClosure K) :=
      (inferInstance : Field (SeparableClosure K)).toSemifield.toCommSemiring
    ∀ [Algebra k (SeparableClosure K)] [Algebra (RatFunc k) (SeparableClosure K)]
      [IsScalarTower k K (SeparableClosure K)]
      [IsScalarTower (RatFunc k) K (SeparableClosure K)]
      [IsScalarTower k (RatFunc k) (SeparableClosure K)]
      (H : FiniteAbstractField Gal(SeparableClosure K/K))
      (T : FiniteGaloisSubextension H.field) [T.field.toSubgroup.Normal],
    let _ : CommSemiring (abstractFixedField K (SeparableClosure K) T.field) :=
      fixedBaseCommSemiring (K := K) (H := T.toFiniteAbstractFieldExtension.field)
    let _ : Algebra K (abstractFixedField K (SeparableClosure K) T.field) :=
      IntermediateField.algebra' (R' := K)
        (abstractFixedField K (SeparableClosure K) T.field)
    let _ : Algebra k (abstractFixedField K (SeparableClosure K) T.field) :=
      IntermediateField.algebra' (R' := k)
        (abstractFixedField K (SeparableClosure K) T.field)
    have _ : FiniteDimensional K (abstractFixedField K (SeparableClosure K) H.field) :=
      abstractFixedField_finiteDimensional K (SeparableClosure K) H.field H.finite
    have _ : FiniteDimensional K (abstractFixedField K (SeparableClosure K) T.field) :=
      abstractFixedField_finiteDimensional K (SeparableClosure K) T.field
        T.toFiniteAbstractFieldExtension.field.finite
    have _ : IsGalois K (abstractFixedField K (SeparableClosure K) T.field) :=
      IsGalois.of_fixedField_normal_subgroup T.field.toSubgroup
    have _ : AlgebraicCurve.HasPrincipalDivisors k
        (abstractFixedField K (SeparableClosure K) T.field) :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K
        (abstractFixedField K (SeparableClosure K) T.field)).toHasPrincipalDivisors
    ∀ c : IdeleClassGroup k K,
      fixedFieldArtin k K (SeparableClosure K) H T
          (IdeleClassGroup.baseChange (k := k) (K := K)
            (L := abstractFixedField K (SeparableClosure K) H.field) c) =
        nativeFixedFieldAbelianizedTransfer K H T
          (finiteArtin k K (abstractFixedField K (SeparableClosure K) T.field) c) := by
  intro closureCommSemiring akΩ aRΩ hkKΩ hRKΩ hkRΩ H T hTnormalGlobal
    cE aKE akE hKF hKE hKEgal hEprincipal c
  let S := finiteAbstractFieldOverIntrinsicBase K H
  let B := intrinsicFiniteAbstractBase K
  let F₀ := abstractFixedField K (SeparableClosure K) B.field
  let F := abstractFixedField K (SeparableClosure K) H.field
  let E := abstractFixedField K (SeparableClosure K) T.field
  have hTB : T.field.toSubgroup ≤ B.field.toSubgroup := T.below.trans S.below
  have hTnormal : (extensionSubgroup B.field T.field hTB).Normal := by
    infer_instance
  have hTfinite : Finite (B.field.toSubgroup ⧸ extensionSubgroup B.field T.field hTB) :=
    (finiteAbstractFieldOverIntrinsicBase K T.toFiniteAbstractFieldExtension.field).finiteQuotient
  let U : FiniteGaloisSubextension B.field := ⟨T.field, hTB, hTnormal, hTfinite⟩
  have hKF₀ : FiniteDimensional K F₀ :=
    (finiteGaloisBaseFixedFieldEquiv K).toLinearEquiv.finiteDimensional
  let aF₀E : Algebra F₀ E := (abstractRelativeFixedField K (SeparableClosure K) hTB).algebra
  let sF₀E : SMul F₀ E := aF₀E.toSMul
  have hKF₀E : IsScalarTower K F₀ E :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hF₀ : Module.finrank K F₀ = 1 := by
    exact (finiteGaloisBaseFixedFieldEquiv K).toLinearEquiv.finrank_eq.symm.trans
      (Module.finrank_self K)
  let e₀ : Gal(E/F₀) ≃* Gal(E/K) :=
    ClassFieldTheory.galoisRestrictScalarsEquivOfFinrankOne hF₀
  let c₀ : IdeleClassGroup k F₀ :=
    IdeleClassGroup.baseChange (k := k) (K := K) (L := F₀) c
  let b : Abelianization Gal(E/F₀) :=
    fixedFieldArtin k K (SeparableClosure K) B U c₀
  have hLower : finiteArtin k K E c = e₀.abelianizationCongr b :=
    finiteArtin_intrinsicBase_equiv k K T.field hTB
      (hSnormal := hTnormal) (hSfinite := hTfinite) c
  have hAmbient :
      fixedFieldArtin k K (SeparableClosure K) H T
          (IdeleClassGroup.baseChange (k := k) (K := K) (L := F) c) =
        fixedFieldAbelianizedTransfer K (SeparableClosure K) S T.field T.below b := by
    with_reducible exact (fixedFieldArtin_baseChange_originalTransfer
      k K (SeparableClosure K) S T (hTnormal := hTnormal) (hTfinite := hTfinite) c)
  have hcancel : fixedFieldAbelianizedTransfer K (SeparableClosure K) S T.field T.below b =
      nativeFixedFieldAbelianizedTransfer K H T (e₀.abelianizationCongr b) :=
    (nativeFixedFieldAbelianizedTransfer_intrinsic K H T b).symm
  exact hAmbient.trans (hcancel.trans
    (congrArg (nativeFixedFieldAbelianizedTransfer K H T) hLower).symm)

/-- Native reciprocity carries actual idele-class inclusion to the original
finite transfer. Only the upper relative quotient is required to be abelian;
the quotient over `K` may be nonabelian. -/
theorem finiteArtin_baseChange_transfer_of_fixedField
    (H : FiniteAbstractField Gal(SeparableClosure K/K))
    (T : FiniteGaloisSubextension H.field)
    [T.field.toSubgroup.Normal] [IsMulCommutative T.extensionQuotient] :
    let _ : CommSemiring (abstractFixedField K (SeparableClosure K) T.field) :=
      fixedBaseCommSemiring (K := K) (H := T.toFiniteAbstractFieldExtension.field)
    let _ : Algebra K (abstractFixedField K (SeparableClosure K) T.field) :=
      IntermediateField.algebra' (R' := K)
        (abstractFixedField K (SeparableClosure K) T.field)
    let akE : Algebra k (abstractFixedField K (SeparableClosure K) T.field) :=
      IntermediateField.algebra' (R' := k)
        (abstractFixedField K (SeparableClosure K) T.field)
    let aFE : Algebra (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) :=
      (abstractRelativeFixedField K (SeparableClosure K) T.below).algebra
    let _ : SMul (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) := aFE.toSMul
    let _ : Module (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) := aFE.toModule
    have _ : IsScalarTower k (abstractFixedField K (SeparableClosure K) H.field)
        (SeparableClosure K) :=
      IsScalarTower.to₁₃₄ k K (abstractFixedField K (SeparableClosure K) H.field)
        (SeparableClosure K)
    have _ : IsScalarTower K (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    have _ : FiniteDimensional K (abstractFixedField K (SeparableClosure K) H.field) :=
      abstractFixedField_finiteDimensional K (SeparableClosure K) H.field H.finite
    have _ : FiniteDimensional K (abstractFixedField K (SeparableClosure K) T.field) :=
      abstractFixedField_finiteDimensional K (SeparableClosure K) T.field
        T.toFiniteAbstractFieldExtension.field.finite
    have _ : IsGalois K (abstractFixedField K (SeparableClosure K) T.field) :=
      IsGalois.of_fixedField_normal_subgroup T.field.toSubgroup
    have hkFE : IsScalarTower k (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) :=
      IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext
        (IsScalarTower.algebraMap_apply k (abstractFixedField K (SeparableClosure K) H.field)
          (SeparableClosure K) x))
    have hFE : FiniteDimensional (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field) :=
      FiniteDimensional.right K (abstractFixedField K (SeparableClosure K) H.field)
        (abstractFixedField K (SeparableClosure K) T.field)
    have hFEgal : @IsGalois (abstractFixedField K (SeparableClosure K) H.field) _
        (abstractFixedField K (SeparableClosure K) T.field) _ aFE :=
      abstractRelativeFixedField_isGalois K (SeparableClosure K)
        H.field T.field T.below T.normal
    have hFprincipal : AlgebraicCurve.HasPrincipalDivisors k
        (abstractFixedField K (SeparableClosure K) H.field) :=
      (isCurveOver k (abstractFixedField K (SeparableClosure K) H.field)).toHasPrincipalDivisors
    have hEprincipal : AlgebraicCurve.HasPrincipalDivisors k
        (abstractFixedField K (SeparableClosure K) T.field) :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K
        (abstractFixedField K (SeparableClosure K) T.field)).toHasPrincipalDivisors
    ∀ c : IdeleClassGroup k K,
      @finiteArtin k (abstractFixedField K (SeparableClosure K) H.field)
          (abstractFixedField K (SeparableClosure K) T.field)
          _ _ _ _ _ akE aFE hkFE _ _ _ hFE hFEgal hFprincipal hEprincipal
          (IdeleClassGroup.baseChange (k := k) (K := K)
            (L := abstractFixedField K (SeparableClosure K) H.field) c) =
        nativeFixedFieldAbelianizedTransfer K H T
          (finiteArtin k K (abstractFixedField K (SeparableClosure K) T.field) c) := by
  intro cE aKE akE aFE sFE mFE hkFA hKFE hKF hKE hKEgal hkFE hFE hFEgal
    hFprincipal hEprincipal c
  exact (finiteArtin_eq_fixedFieldArtin k K H T
    (IdeleClassGroup.baseChange (k := k) (K := K)
      (L := abstractFixedField K (SeparableClosure K) H.field) c)).trans
    (fixedFieldArtin_baseChange_nativeTransfer k K H T c)

end NativeArtin

end FunctionField

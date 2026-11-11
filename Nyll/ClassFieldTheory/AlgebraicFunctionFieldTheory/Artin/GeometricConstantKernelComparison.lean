/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricConstantArtinKernels
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayTower
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.GeometricConstantTower
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
public import Mathlib.FieldTheory.IntermediateField.Basic

/-!
# Comparing native kernels in a common actual constant stage

Two finite constant stages embed in a constructed common stage. Their native
Artin kernels map there by the original restricted-ray base change, followed
only by the proved equality between iterated and direct boundary pullbacks.

Equality of the corresponding units in the geometric constant extension is
exactly equality after these native transitions. The proof uses the existing
principal-kernel equivalences to verify the original maps, rather than to
define new transition maps.
-/

@[expose] public section


noncomputable section

open AlgebraicCurve

namespace FunctionField.RayClass

private theorem units_map_inclusionAlgebra
    {B A : Type*} [Field B] [Field A] [Algebra B A]
    (E H : IntermediateField B A) (h : E ≤ H) :
    let _ : Algebra E H := (IntermediateField.inclusion h).toRingHom.toAlgebra
    ∀ x : Eˣ, Units.map (algebraMap E H) x =
      Units.map (IntermediateField.inclusion h).toMonoidHom x := by
  intro aEH x
  rfl

private theorem inclusion_units_eq_iff
    {B A : Type*} [Field B] [Field A] [Algebra B A]
    (E F H G : IntermediateField B A) (iE : E →ₐ[B] G) (iF : F →ₐ[B] G)
    (hiE : ∀ x : E, Subtype.val (iE x) = Subtype.val x)
    (hiF : ∀ x : F, Subtype.val (iF x) = Subtype.val x)
    (hEH : E ≤ H) (hFH : F ≤ H) (x : Eˣ) (y : Fˣ) :
    Units.map iE.toMonoidHom x = Units.map iF.toMonoidHom y ↔
      Units.map (IntermediateField.inclusion hEH).toMonoidHom x =
        Units.map (IntermediateField.inclusion hFH).toMonoidHom y := by
  constructor
  · intro h
    apply Units.ext
    apply Subtype.ext
    have hv := congrArg (fun z : Gˣ => Subtype.val z.val) h
    change Subtype.val (iE (x : E)) = Subtype.val (iF (y : F)) at hv
    exact (hiE (x : E)).symm.trans (hv.trans (hiF (y : F)))
  · intro h
    apply Units.ext
    apply Subtype.ext
    have hv := congrArg (fun z : Hˣ => Subtype.val z.val) h
    change Subtype.val (x : E) = Subtype.val (y : F) at hv
    exact (hiE (x : E)).trans (hv.trans (hiF (y : F)).symm)

section KernelCalculation

variable {k L : Type*} [Field k] [Finite k] [Field L] [Algebra k L]
    [HasPrincipalDivisors k L] [Algebra (RatFunc k) L]
    [IsScalarTower k (RatFunc k) L] [FunctionField k L]

private theorem principalArtinKernelCongr_equiv {m n : Modulus k L} (h : m = n)
    (hm : m ≠ 0) (hn : n ≠ 0) (x : Lˣ) :
    principalArtinKernelCongr h (principalRestrictedArtinKernelEquiv m hm x) =
      principalRestrictedArtinKernelEquiv n hn x := by
  subst n
  rfl

end KernelCalculation

section NativeTransition

variable {k K E H : Type*} [Field k] [Finite k] [Field K] [Field E] [Field H]
    [Algebra k K] [Algebra k E] [Algebra k H]
    [Algebra K E] [Algebra E H] [Algebra K H]
    [IsScalarTower k K E] [IsScalarTower k E H] [IsScalarTower k K H]
    [IsScalarTower K E H]
    [FiniteDimensional K E] [FiniteDimensional E H] [FiniteDimensional K H]
    [HasPrincipalDivisors k E] [HasPrincipalDivisors k H]
    [Algebra (RatFunc k) E] [IsScalarTower k (RatFunc k) E] [FunctionField k E]
    [Algebra (RatFunc k) H] [IsScalarTower k (RatFunc k) H] [FunctionField k H]

theorem nativeTransition_principal
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (hmzero : m ≠ 0) (x : Eˣ) :
    principalArtinKernelCongr (rayModulusBaseChange_trans (L := E) (M := H) m)
        (principalArtinKernelBaseChange (L := H) (rayModulusBaseChange E m)
          (rayModulusBaseChange_reduced m hm)
          (principalRestrictedArtinKernelEquiv (rayModulusBaseChange E m)
            (rayModulusBaseChange_ne_zero m hmzero) x)) =
      principalRestrictedArtinKernelEquiv (rayModulusBaseChange H m)
        (rayModulusBaseChange_ne_zero m hmzero) (Units.map (algebraMap E H) x) := by
  have hbase := principalArtinKernelBaseChange_equiv (k := k) (K := E) (L := H)
    (rayModulusBaseChange E m) (rayModulusBaseChange_reduced m hm)
    (rayModulusBaseChange_ne_zero (L := E) m hmzero) x
  have hcast := congrArg
    (fun a : (restrictedProductAbsoluteArtin
        (rayModulusBaseChange H (rayModulusBaseChange E m))).ker =>
      principalArtinKernelCongr (rayModulusBaseChange_trans (L := E) (M := H) m) a) hbase
  have htarget := principalArtinKernelCongr_equiv (k := k) (L := H)
    (m := rayModulusBaseChange H (rayModulusBaseChange E m))
    (n := rayModulusBaseChange H m)
    (rayModulusBaseChange_trans (L := E) (M := H) m)
    (rayModulusBaseChange_ne_zero (L := H) (rayModulusBaseChange E m)
      (rayModulusBaseChange_ne_zero (L := E) m hmzero))
    (rayModulusBaseChange_ne_zero (L := H) m hmzero) (Units.map (algebraMap E H) x)
  exact hcast.trans htarget

end NativeTransition

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]

/-- Equality of geometric function units from two actual finite constant stages
is detected in a common native Artin kernel using the original ray transitions. -/
theorem geometricConstantKernelImages_eq_iff_common_stage
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (hmzero : m ≠ 0) (n₁ n₂ : ℕ+) :
    ∃ n₃ : ℕ+,
    ∃ h₁ : (fullConstantDegreeStage k K Ω n₁).toIntermediateField ≤
      (fullConstantDegreeStage k K Ω n₃).toIntermediateField,
    ∃ h₂ : (fullConstantDegreeStage k K Ω n₂).toIntermediateField ≤
      (fullConstantDegreeStage k K Ω n₃).toIntermediateField,
      let E := fullConstantDegreeStage k K Ω n₁
      let F := fullConstantDegreeStage k K Ω n₂
      let H := fullConstantDegreeStage k K Ω n₃
      let pE := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K E
      let _ : Algebra (RatFunc k) E := pE.val
      let _ : IsScalarTower k (RatFunc k) E := pE.property.1
      let _ : FunctionField k E := pE.property.2
      let _ : HasPrincipalDivisors k E :=
        (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K E).toHasPrincipalDivisors
      let pF := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K F
      let _ : Algebra (RatFunc k) F := pF.val
      let _ : IsScalarTower k (RatFunc k) F := pF.property.1
      let _ : FunctionField k F := pF.property.2
      let _ : HasPrincipalDivisors k F :=
        (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K F).toHasPrincipalDivisors
      let pH := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K H
      let _ : Algebra (RatFunc k) H := pH.val
      let _ : IsScalarTower k (RatFunc k) H := pH.property.1
      let _ : FunctionField k H := pH.property.2
      let _ : HasPrincipalDivisors k H :=
        (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K H).toHasPrincipalDivisors
      let _ : Algebra E H := (IntermediateField.inclusion h₁).toRingHom.toAlgebra
      let _ : IsScalarTower K E H :=
        IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
      let _ : IsScalarTower k E H :=
        IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
      let _ : FiniteDimensional E H := FiniteDimensional.right K E H
      let _ : Algebra F H := (IntermediateField.inclusion h₂).toRingHom.toAlgebra
      let _ : IsScalarTower K F H :=
        IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
      let _ : IsScalarTower k F H :=
        IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl
      let _ : FiniteDimensional F H := FiniteDimensional.right K F H
      let eE := principalRestrictedArtinKernelEquiv (rayModulusBaseChange E m)
        (rayModulusBaseChange_ne_zero m hmzero)
      let eF := principalRestrictedArtinKernelEquiv (rayModulusBaseChange F m)
        (rayModulusBaseChange_ne_zero m hmzero)
      let tE := (principalArtinKernelCongr
        (rayModulusBaseChange_trans (L := E) (M := H) m)).toMonoidHom.comp
          (principalArtinKernelBaseChange (L := H) (rayModulusBaseChange E m)
            (rayModulusBaseChange_reduced m hm))
      let tF := (principalArtinKernelCongr
        (rayModulusBaseChange_trans (L := F) (M := H) m)).toMonoidHom.comp
          (principalArtinKernelBaseChange (L := H) (rayModulusBaseChange F m)
            (rayModulusBaseChange_reduced m hm))
      let iE : E →ₐ[K] geometricConstantExtension k K Ω :=
        fullConstantStageGeometricInclusion k K Ω n₁
      let iF : F →ₐ[K] geometricConstantExtension k K Ω :=
        fullConstantStageGeometricInclusion k K Ω n₂
      let fE := (Units.map iE.toMonoidHom).comp eE.symm.toMonoidHom
      let fF := (Units.map iF.toMonoidHom).comp eF.symm.toMonoidHom
      ∀ a b, fE a = fF b ↔ tE a = tF b := by
  obtain ⟨n₃, h₁, h₂⟩ := fullConstantDegreeStage_directed k K Ω n₁ n₂
  refine ⟨n₃, h₁, h₂, ?_⟩
  intro E F H pE aRE hkRE hE hpE pF aRF hkRF hF hpF pH aRH hkRH hH hpH
    aEH hKEH hkEH hEH aFH hKFH hkFH hFH eE eF tE tF iE iF fE fF a b
  let eH := principalRestrictedArtinKernelEquiv (rayModulusBaseChange H m)
    (rayModulusBaseChange_ne_zero m hmzero)
  obtain ⟨x, rfl⟩ := eE.surjective a
  obtain ⟨y, rfl⟩ := eF.surjective b
  have htENative :=
    nativeTransition_principal (k := k) (K := K) (E := E) (H := H) m hm hmzero x
  have hincludeE := units_map_inclusionAlgebra (B := K) (A := Ω)
    E.toIntermediateField H.toIntermediateField h₁ x
  have htE := htENative.trans (congrArg (fun z : Hˣ => eH z) hincludeE)
  have htFNative :=
    nativeTransition_principal (k := k) (K := K) (E := F) (H := H) m hm hmzero y
  have hincludeF := units_map_inclusionAlgebra (B := K) (A := Ω)
    F.toIntermediateField H.toIntermediateField h₂ y
  have htF := htFNative.trans (congrArg (fun z : Hˣ => eH z) hincludeF)
  have hvE : fE (eE x) = Units.map iE.toMonoidHom x :=
    congrArg (Units.map iE.toMonoidHom) (eE.symm_apply_apply x)
  have hvF : fF (eF y) = Units.map iF.toMonoidHom y :=
    congrArg (Units.map iF.toMonoidHom) (eF.symm_apply_apply y)
  have hiE : ∀ z : E, Subtype.val (iE z) = Subtype.val z :=
    fullConstantStageGeometricInclusion_coe k K Ω n₁
  have hiF : ∀ z : F, Subtype.val (iF z) = Subtype.val z :=
    fullConstantStageGeometricInclusion_coe k K Ω n₂
  rw [hvE, hvF]
  dsimp only [tE, tF, eE, eF, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [htE, htF]
  exact (inclusion_units_eq_iff (B := K) (A := Ω) E.toIntermediateField F.toIntermediateField
    H.toIntermediateField (geometricConstantExtension k K Ω) iE iF hiE hiF h₁ h₂ x y).trans
      eH.injective.eq_iff.symm

end FunctionField.RayClass

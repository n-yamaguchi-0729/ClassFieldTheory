/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.DegreeOneAbsoluteGalois
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteArtinTransfer
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.DegreeOneArtinNaturality
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTower
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionIntermediate
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve

/-!
# Native original transfer for an actual presentation of the fixed field

A degree-one inclusion of the original upper field into its actual fixed
field presentation does not change its native reciprocity. The proved
degree-one comparison therefore expresses original transfer with values
in the original upper field, while retaining the literal action on the
ambient separable closure.
-/

@[expose] public section

noncomputable section

universe u v w

namespace FunctionField

open AlgebraicCurve ClassFormation LocalClassFieldTheory ProCGroups.Abelian
open ProCGroups.FiniteStepSolvableQuotients

-- These comparisons use the proved Artin formulas rather than unfolding their construction.
attribute [local irreducible] abelianFiniteArtin finiteArtin

section Groups

variable (K : Type u) (L : Type v) [Field K] [Field L]
  (H : FiniteAbstractField Gal(SeparableClosure K/K)) [H.field.toSubgroup.Normal]

local notation "F" => abstractFixedField K (SeparableClosure K) H.field

/-- The canonical separable-closure algebra of the actual fixed field. -/
local instance presentedFixedFieldSeparableClosureAlgebra : Algebra F (SeparableClosure F) :=
  (separableClosure F (AlgebraicClosure F)).toSubalgebra.algebra

/-- The fixed field acts on its closure through that same canonical algebra. -/
local instance presentedFixedFieldSeparableClosureSMul : SMul F (SeparableClosure F) :=
  (presentedFixedFieldSeparableClosureAlgebra (K := K) (H := H)).toSMul

variable [Algebra L (abstractFixedField K (SeparableClosure K) H.field)]
  [Algebra L (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))]
  [IsScalarTower L (abstractFixedField K (SeparableClosure K) H.field)
    (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))]
  (hLF : Module.finrank L (abstractFixedField K (SeparableClosure K) H.field) = 1)
  (eF : SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)
    ≃ₐ[(abstractFixedField K (SeparableClosure K) H.field)] SeparableClosure K)
  (eL : SeparableClosure (abstractFixedField K (SeparableClosure K) H.field) ≃ₐ[L]
    SeparableClosure L)

/-- The original upper field's native absolute Galois group, identified
with the original finite-index subgroup using its actual presentation. -/
def presentedFixedFieldAbsoluteGaloisEquiv :
    Gal(SeparableClosure L/L) ≃ₜ* H.field.toSubgroup :=
  (degreeOneAbsoluteGaloisEquiv L F hLF eL).symm.trans
    (fixedFieldAbsoluteGaloisEquivOfClosure K (SeparableClosure K) H eF)

omit [H.field.toSubgroup.Normal] in
/-- The comparison retains the literal composite closure conjugation. -/
theorem presentedFixedFieldAbsoluteGaloisEquiv_apply
    (σ : Gal(SeparableClosure L/L)) (x : SeparableClosure K) :
    (presentedFixedFieldAbsoluteGaloisEquiv K L H hLF eF eL σ).val x =
      eF (eL.symm (σ (eL (eF.symm x)))) := by
  change eF (((degreeOneAbsoluteGaloisEquiv L F hLF eL).symm σ)
    (eF.symm x)) = _
  rw [degreeOneAbsoluteGaloisEquiv_symm_apply]

-- Subsequent comparisons use the equivalences through their representative formulas.
attribute [local irreducible]
  degreeOneAbsoluteGaloisEquiv fixedFieldAbsoluteGaloisEquivOfClosure

/-- The actual presentation induces the corresponding abelian comparison. -/
def presentedFixedFieldAbsoluteAbelianEquiv :
    localAbsoluteAbelianProfinite L ≃ₜ* TopologicalAbelianization H.field.toSubgroup :=
  TopologicalAbelianization.congr
    (presentedFixedFieldAbsoluteGaloisEquiv K L H hLF eF eL)

omit [H.field.toSubgroup.Normal] in
/-- The two actual field comparisons compose on original abelian representatives. -/
theorem presentedFixedFieldAbsoluteAbelianEquiv_degreeOne
    (a : localAbsoluteAbelianProfinite F) :
    presentedFixedFieldAbsoluteAbelianEquiv K L H hLF eF eL
        (degreeOneAbsoluteAbelianEquiv L F hLF eL a) =
      fixedFieldAbsoluteAbelianEquivOfClosure K (SeparableClosure K) H eF a := by
  let eD : Gal(SeparableClosure F/F) ≃ₜ* Gal(SeparableClosure L/L) :=
    degreeOneAbsoluteGaloisEquiv L F hLF eL
  let eFix : Gal(SeparableClosure F/F) ≃ₜ* H.field.toSubgroup :=
    fixedFieldAbsoluteGaloisEquivOfClosure K (SeparableClosure K) H eF
  refine QuotientGroup.induction_on a ?_
  intro σ
  rw [degreeOneAbsoluteAbelianEquiv_mk,
    fixedFieldAbsoluteAbelianEquivOfClosure_mk]
  have hcancel : presentedFixedFieldAbsoluteGaloisEquiv K L H hLF eF eL (eD σ) =
      eFix σ :=
    congrArg eFix (eD.symm_apply_apply σ)
  exact (TopologicalAbelianization.congr_apply_mk
    (presentedFixedFieldAbsoluteGaloisEquiv K L H hLF eF eL) (eD σ)).trans
      (congrArg (TopologicalAbelianization.mk H.field.toSubgroup) hcancel)

/-- Original native transfer with target the actual upper field rather
than only the subtype used to present its fixed field. -/
def nativeAbsoluteTransferOfDegreeOnePresentation :
    localAbsoluteAbelianProfinite K →ₜ* localAbsoluteAbelianProfinite L :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (degreeOneAbsoluteAbelianEquiv L F hLF eL)).comp
      (nativeAbsoluteTransferOfFixedField K H eF)

/-- This map is the original subgroup transfer under the actual original
Galois comparison; the equality follows on the unchanged group representatives. -/
theorem nativeAbsoluteTransferOfDegreeOnePresentation_comparison :
    have _ : Finite (Gal(SeparableClosure K/K) ⧸ H.field.toSubgroup) :=
      ambientQuotientFiniteOfAbstractFinite K (SeparableClosure K) H.field H.finite
    ∀ a : localAbsoluteAbelianProfinite K,
      presentedFixedFieldAbsoluteAbelianEquiv K L H hLF eF eL
          (nativeAbsoluteTransferOfDegreeOnePresentation K L H hLF eF eL a) =
        openNormalTransferTopologicalAbelianization
          (finiteAbstractOpenNormal K (SeparableClosure K) H) a := by
  intro hfinite a
  change presentedFixedFieldAbsoluteAbelianEquiv K L H hLF eF eL
      (degreeOneAbsoluteAbelianEquiv L F hLF eL
        (nativeAbsoluteTransferOfFixedField K H eF a)) = _
  rw [presentedFixedFieldAbsoluteAbelianEquiv_degreeOne]
  exact (fixedFieldAbsoluteAbelianEquivOfClosure K (SeparableClosure K) H eF).apply_symm_apply _

end Groups

section Reciprocity

variable (k : Type w) (K : Type u) (L : Type v) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
  [FiniteDimensional K L] [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
  (H : FiniteAbstractField Gal(SeparableClosure K/K)) [H.field.toSubgroup.Normal]

local notation "F" => abstractFixedField K (SeparableClosure K) H.field

attribute [local instance]
  presentedFixedFieldSeparableClosureAlgebra presentedFixedFieldSeparableClosureSMul

variable [Algebra L (abstractFixedField K (SeparableClosure K) H.field)]
  [IsScalarTower K L (abstractFixedField K (SeparableClosure K) H.field)]
  [Algebra L (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))]
  [IsScalarTower L (abstractFixedField K (SeparableClosure K) H.field)
    (SeparableClosure (abstractFixedField K (SeparableClosure K) H.field))]
  (hLF : Module.finrank L (abstractFixedField K (SeparableClosure K) H.field) = 1)
  (eF : SeparableClosure (abstractFixedField K (SeparableClosure K) H.field)
    ≃ₐ[(abstractFixedField K (SeparableClosure K) H.field)] SeparableClosure K)
  (eL : SeparableClosure (abstractFixedField K (SeparableClosure K) H.field) ≃ₐ[L]
    SeparableClosure L)

/-- The original Artin map of the actual upper field carries actual
idele inclusion to original group transfer through its proved degree-one
fixed-field presentation. -/
theorem absoluteArtin_baseChange_presentedTransfer (c : IdeleClassGroup k K) :
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
    have _ : FiniteDimensional K F :=
      abstractFixedField_finiteDimensional K (SeparableClosure K) H.field H.finite
    have _ : FunctionField k F :=
      IdeleClassGroup.FiniteExtensionLimit.intermediateFunctionField
        (k := k) (K := K) (Ω := SeparableClosure K) F
    have _ : HasPrincipalDivisors k F :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K F).toHasPrincipalDivisors
    have _ : IsGalois K F :=
      IsGalois.of_fixedField_normal_subgroup H.field.toSubgroup
    absoluteArtin k L
        (IdeleClassGroup.baseChange (k := k) (K := K) (L := L) c) =
      nativeAbsoluteTransferOfDegreeOnePresentation K L H hLF eF eL
        (absoluteArtin k K c) := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ hKF hFfield hFprincipal hFgal
  have hkLF : IsScalarTower k L F := IsScalarTower.to₁₃₄ k K L F
  have hLFfinite : FiniteDimensional L F := FiniteDimensional.right K L F
  have hLFgalois : IsGalois L F := IsGalois.tower_top_of_isGalois K L F
  rw [← absoluteArtin_baseChange_of_finrank_one k L F hLF eL
    (IdeleClassGroup.baseChange (k := k) (K := K) (L := L) c),
    IdeleClassGroup.baseChange_trans]
  exact congrArg (degreeOneAbsoluteAbelianEquiv L F hLF eL)
    (absoluteArtin_baseChange_nativeTransfer k K H eF c)

end Reciprocity

end FunctionField

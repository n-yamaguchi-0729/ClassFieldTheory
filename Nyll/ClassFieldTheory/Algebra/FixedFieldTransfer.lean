/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.FiniteAbstractFixedField
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main

/-!
# Finite transfer on the abelianizations of actual fixed fields
-/

@[expose] public section

universe v w

noncomputable section

namespace FunctionField

open ClassFormation CyclicCohomology LocalClassFieldTheory
open scoped IsMulCommutative

section FiniteTransfer

variable (K : Type v) (Ω : Type w) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (T : FiniteAbstractFieldExtension Gal(Ω/K)) (U : ClosedSubgroup Gal(Ω/K))
    (hU : U.toSubgroup ≤ T.field.field.toSubgroup)
    [hUnormal : (extensionSubgroup T.base.field U (hU.trans T.below)).Normal]
    [hUfinite : Finite (T.base.field.toSubgroup ⧸
      extensionSubgroup T.base.field U (hU.trans T.below))]

/-- The original finite group transfer, with values in the actual relative
Galois abelianizations of the same fixed fields. -/
def fixedFieldAbelianizedTransfer :
    Group.Abelianization Gal((abstractRelativeFixedField K Ω (hU.trans T.below))/
      (abstractFixedField K Ω T.base.field)) →*
    Group.Abelianization Gal((abstractRelativeFixedField K Ω hU)/
      (abstractFixedField K Ω T.field.field)) := by
  have hUnormal' : (extensionSubgroup T.field.field U hU).Normal :=
    transferNormNaturality_intermediateExtension_normal
      T.base.field T.field.field U hU T.below
  let eH := abstractExtensionQuotientEquivGaloisGroup
    K Ω T.base.field U (hU.trans T.below) hUnormal
  let eJ := abstractExtensionQuotientEquivGaloisGroup
    K Ω T.field.field U hU hUnormal'
  exact eJ.abelianizationCongr.toMonoidHom.comp
    ((transferNormNaturalityTransfer T.base.field T.field.field U hU T.below).comp
      eH.abelianizationCongr.symm.toMonoidHom)

/-- On the original quotient representative the map is precisely finite group transfer. -/
theorem fixedFieldAbelianizedTransfer_apply
    (x : Group.Abelianization (T.base.field.toSubgroup ⧸
      extensionSubgroup T.base.field U (hU.trans T.below))) :
    let hUnormal' : (extensionSubgroup T.field.field U hU).Normal :=
      transferNormNaturality_intermediateExtension_normal
        T.base.field T.field.field U hU T.below
    fixedFieldAbelianizedTransfer K Ω T U hU
        ((abstractExtensionQuotientEquivGaloisGroup K Ω T.base.field U
          (hU.trans T.below) hUnormal).abelianizationCongr x) =
      (abstractExtensionQuotientEquivGaloisGroup K Ω T.field.field U
        hU hUnormal').abelianizationCongr
          (transferNormNaturalityTransfer T.base.field T.field.field U hU T.below x) := by
  intro hUnormal'
  change (abstractExtensionQuotientEquivGaloisGroup K Ω T.field.field U
      hU hUnormal').abelianizationCongr
    (transferNormNaturalityTransfer T.base.field T.field.field U hU T.below
      ((abstractExtensionQuotientEquivGaloisGroup K Ω T.base.field U
        (hU.trans T.below) hUnormal).abelianizationCongr.symm
        ((abstractExtensionQuotientEquivGaloisGroup K Ω T.base.field U
          (hU.trans T.below) hUnormal).abelianizationCongr x))) = _
  rw [MulEquiv.symm_apply_apply]

end FiniteTransfer

end FunctionField

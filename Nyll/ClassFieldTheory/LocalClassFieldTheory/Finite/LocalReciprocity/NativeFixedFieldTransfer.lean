/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.FixedFieldTransfer
public import Nyll.ClassFieldTheory.Algebra.GaloisRestrictionFinrankOne
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisPresentation

/-!
# Native finite transfer over the original field
-/

@[expose] public section

universe v

noncomputable section

namespace FunctionField

open ClassFormation CyclicCohomology LocalClassFieldTheory

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
    Group.Abelianization Gal((abstractFixedField K (SeparableClosure K) T.field)/K) →*
      Group.Abelianization Gal((abstractRelativeFixedField K (SeparableClosure K) T.below)/
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

end NativeTransfer

end FunctionField

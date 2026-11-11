/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldSymbol
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.Representation
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionIntermediateTower
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main

/-!
# Actual fixed-field Artin symbols and finite transfer

The original inclusion of idele classes is carried by fixed-coefficient
descent to the original inclusion of fixed elements. The proved abstract
transfer naturality therefore gives the finite Artin square on actual
fixed fields. Its Galois arrow is the existing group transfer, expressed
through the original quotient-to-relative-Galois equivalences.

This identifies the finite arithmetic transition needed for constant
stages. Neither a function-group transition square nor compatibility of
the actual Artin maps with transfer is assumed.
-/

@[expose] public section

universe u v w

noncomputable section

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology
open FunctionField.IdeleClassGroup.FiniteExtensionLimit

namespace FunctionField

section FixedCoefficients

variable (k : Type u) (K : Type v) (Ω : Type w)
    [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [FunctionField k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω]

/-- Actual idele-class inclusion is the original inclusion of fixed coefficients. -/
theorem abstractFixedClassEquiv_baseChange (H J : FiniteAbstractField Gal(Ω/K))
    (hJH : J.field.toSubgroup ≤ H.field.toSubgroup) :
    let _ : FiniteDimensional K (abstractFixedField K Ω H.field) :=
      abstractFixedField_finiteDimensional K Ω H.field H.finite
    let _ : FiniteDimensional K (abstractFixedField K Ω J.field) :=
      abstractFixedField_finiteDimensional K Ω J.field J.finite
    let _ : Algebra (abstractFixedField K Ω H.field) (abstractFixedField K Ω J.field) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω hJH)).toRingHom.toAlgebra
    let _ : IsScalarTower K (abstractFixedField K Ω H.field)
        (abstractFixedField K Ω J.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : IsScalarTower k (abstractFixedField K Ω H.field)
        (abstractFixedField K Ω J.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : FiniteDimensional (abstractFixedField K Ω H.field)
        (abstractFixedField K Ω J.field) := FiniteDimensional.right K _ _
    let _ : Algebra.IsSeparable (abstractFixedField K Ω H.field)
        (abstractFixedField K Ω J.field) :=
      Algebra.isSeparable_tower_top_of_isSeparable K _ _
    ∀ c : Additive (IdeleClassGroup k (abstractFixedField K Ω H.field)),
      abstractFixedClassEquiv k K Ω J.field J.finite
          (Additive.ofMul (IdeleClassGroup.baseChange (k := k)
            (K := abstractFixedField K Ω H.field)
            (L := abstractFixedField K Ω J.field) c.toMul)) =
        fixedFieldInclusion (ideleClassRepresentation k K Ω) H.field J.field hJH
          (abstractFixedClassEquiv k K Ω H.field H.finite c) := by
  intro hFfinite hEfinite aFE hKFE hkFE hFEfinite hFEsep c
  apply Subtype.ext
  change (abstractFixedClassEquiv k K Ω J.field J.finite
      (Additive.ofMul (IdeleClassGroup.baseChange (k := k)
        (K := abstractFixedField K Ω H.field)
        (L := abstractFixedField K Ω J.field) c.toMul))).val =
    (abstractFixedClassEquiv k K Ω H.field H.finite c).val
  rw [abstractFixedClassEquiv_coe, abstractFixedClassEquiv_coe]
  exact congrArg Additive.ofMul
    (ofIntermediate_baseChange (abstractFixedField K Ω H.field)
      (abstractFixedField K Ω J.field) (abstractFixedField_le K Ω hJH) c.toMul)

end FixedCoefficients

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
    Abelianization Gal((abstractRelativeFixedField K Ω (hU.trans T.below))/
      (abstractFixedField K Ω T.base.field)) →*
    Abelianization Gal((abstractRelativeFixedField K Ω hU)/
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
    (x : Abelianization (T.base.field.toSubgroup ⧸
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

section ArtinTransfer

variable (k : Type u) (K : Type v) (Ω : Type w)
    [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω] [IsSepClosed Ω]

/-- The original Artin symbol of actual idele-class inclusion is the
original finite transfer of the lower Artin symbol. -/
theorem fixedFieldArtin_baseChange_transfer
    (T : FiniteAbstractFieldExtension Gal(Ω/K)) (U : ClosedSubgroup Gal(Ω/K))
    (hU : U.toSubgroup ≤ T.field.field.toSubgroup)
    [hUnormal : (extensionSubgroup T.base.field U (hU.trans T.below)).Normal]
    [hUfinite : Finite (T.base.field.toSubgroup ⧸
      extensionSubgroup T.base.field U (hU.trans T.below))] :
    let hUnormal' : (extensionSubgroup T.field.field U hU).Normal :=
      transferNormNaturality_intermediateExtension_normal
        T.base.field T.field.field U hU T.below
    let hUfinite' : Finite (T.field.field.toSubgroup ⧸
        extensionSubgroup T.field.field U hU) :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion T.base.field T.field.field U hU T.below)
        (transferNormNaturalityIntermediateInclusion_injective
          T.base.field T.field.field U hU T.below)
    let _ : FiniteDimensional K (abstractFixedField K Ω T.base.field) :=
      abstractFixedField_finiteDimensional K Ω T.base.field T.base.finite
    let _ : FiniteDimensional K (abstractFixedField K Ω T.field.field) :=
      abstractFixedField_finiteDimensional K Ω T.field.field T.field.finite
    let _ : Algebra (abstractFixedField K Ω T.base.field)
        (abstractFixedField K Ω T.field.field) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω T.below)).toRingHom.toAlgebra
    let _ : IsScalarTower K (abstractFixedField K Ω T.base.field)
        (abstractFixedField K Ω T.field.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : IsScalarTower k (abstractFixedField K Ω T.base.field)
        (abstractFixedField K Ω T.field.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : FiniteDimensional (abstractFixedField K Ω T.base.field)
        (abstractFixedField K Ω T.field.field) := FiniteDimensional.right K _ _
    let _ : Algebra.IsSeparable (abstractFixedField K Ω T.base.field)
        (abstractFixedField K Ω T.field.field) :=
      Algebra.isSeparable_tower_top_of_isSeparable K _ _
    ∀ c : IdeleClassGroup k (abstractFixedField K Ω T.base.field),
      fixedFieldArtin k K Ω T.field ⟨U, hU, hUnormal', hUfinite'⟩
          (IdeleClassGroup.baseChange (k := k)
            (K := abstractFixedField K Ω T.base.field)
            (L := abstractFixedField K Ω T.field.field) c) =
        fixedFieldAbelianizedTransfer K Ω T U hU
          (fixedFieldArtin k K Ω T.base
            ⟨U, hU.trans T.below, hUnormal, hUfinite⟩ c) := by
  intro hUnormal' hUfinite' hFfinite hEfinite aFE hKFE hkFE hFEfinite hFEsep c
  let A := ideleClassRepresentation k K Ω
  let D := fullConstantDegreeData k K Ω
  let v := ideleClassValuationData k K Ω
  have hcf := ideleClassRepresentation_satisfiesClassFieldAxiom k K Ω
  let E : FiniteGaloisSubextension T.base.field :=
    ⟨U, hU.trans T.below, hUnormal, hUfinite⟩
  let E' : FiniteGaloisSubextension T.field.field := ⟨U, hU, hUnormal', hUfinite'⟩
  let eH := abstractExtensionQuotientEquivGaloisGroup K Ω T.base.field U
    (hU.trans T.below) hUnormal
  let eJ := abstractExtensionQuotientEquivGaloisGroup K Ω T.field.field U hU hUnormal'
  let a := abstractFixedClassEquiv k K Ω T.base.field T.base.finite (Additive.ofMul c)
  let z := ((D.normResidueSymbol A v hcf T.base E)
    (finiteNormClass A T.base.field U (hU.trans T.below) a)).toMul
  have h := DFunLike.congr_fun
    (D.normResidueNaturality_transfer_inclusion A v hcf T U hU)
    (finiteNormClass A T.base.field U (hU.trans T.below) a)
  change Additive.ofMul
      (transferNormNaturalityTransfer T.base.field T.field.field U hU T.below z) =
    (D.normResidueSymbol A v hcf T.field E')
      (transferNormNaturalityNormQuotientInclusion A T.base.field T.field.field U
        hU T.below (finiteNormClass A T.base.field U (hU.trans T.below) a)) at h
  have hq := transferNormNaturality_normQuotientInclusion_finiteNormClass
    A T.base.field T.field.field U hU T.below a
  have hinc := abstractFixedClassEquiv_baseChange k K Ω T.base T.field T.below
    (Additive.ofMul c)
  have hclass := hq.trans
    (congrArg (finiteNormClass A T.field.field U hU) hinc.symm)
  have hsymbol := h.trans
    (congrArg (D.normResidueSymbol A v hcf T.field E') hclass)
  change eJ.abelianizationCongr
      ((D.normResidueSymbol A v hcf T.field E')
        (finiteNormClass A T.field.field U hU
          (abstractFixedClassEquiv k K Ω T.field.field T.field.finite
            (Additive.ofMul (IdeleClassGroup.baseChange (k := k)
              (K := abstractFixedField K Ω T.base.field)
              (L := abstractFixedField K Ω T.field.field) c))))).toMul =
    fixedFieldAbelianizedTransfer K Ω T U hU (eH.abelianizationCongr z)
  exact (congrArg eJ.abelianizationCongr (congrArg Additive.toMul hsymbol)).symm.trans
    (fixedFieldAbelianizedTransfer_apply K Ω T U hU z).symm

end ArtinTransfer

end FunctionField

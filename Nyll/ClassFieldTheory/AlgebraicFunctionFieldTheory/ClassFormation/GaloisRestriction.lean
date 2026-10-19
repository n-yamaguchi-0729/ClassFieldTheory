/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality

/-!
# Actual Galois restriction between fixed fields

Restriction in the abstract finite Galois quotients agrees with restriction
of automorphisms of the actual fixed fields. The comparison is proved on
ambient automorphism representatives.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- Restriction of an actual fixed-field automorphism preserves its ambient representative. -/
theorem abstractFixedField_restrictNormal_quotient_mk
    (H J U : ClosedSubgroup Gal(Ω/K))
    (hJH : J.toSubgroup ≤ H.toSubgroup) (hUH : U.toSubgroup ≤ H.toSubgroup)
    (hUJ : U.toSubgroup ≤ J.toSubgroup)
    (hJnormal : (extensionSubgroup H J hJH).Normal)
    (hUnormal : (extensionSubgroup H U hUH).Normal) :
    let _ := hJnormal
    let _ := hUnormal
    let _ : Algebra (abstractFixedField K Ω H) (abstractFixedField K Ω J) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω hJH)).toRingHom.toAlgebra
    let _ : Algebra (abstractFixedField K Ω H) (abstractFixedField K Ω U) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω hUH)).toRingHom.toAlgebra
    let _ : Algebra (abstractFixedField K Ω J) (abstractFixedField K Ω U) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω hUJ)).toRingHom.toAlgebra
    let _ : IsScalarTower (abstractFixedField K Ω H) (abstractFixedField K Ω J)
        (abstractFixedField K Ω U) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : IsGalois (abstractFixedField K Ω H) (abstractFixedField K Ω J) :=
      abstractRelativeFixedField_isGalois K Ω H J hJH hJnormal
    ∀ σ : H.toSubgroup,
      AlgEquiv.restrictNormalHom (F := abstractFixedField K Ω H)
          (K₁ := abstractFixedField K Ω U) (abstractFixedField K Ω J)
          (abstractExtensionQuotientEquivGaloisGroup K Ω H U hUH hUnormal
            (QuotientGroup.mk σ)) =
        abstractExtensionQuotientEquivGaloisGroup K Ω H J hJH hJnormal
          (QuotientGroup.mk σ) := by
  intro hnJ hnU aFJ aFU aJU hFJU hgal σ
  apply AlgEquiv.ext
  intro x
  apply Subtype.val_injective
  let τ : Gal((abstractFixedField K Ω U)/(abstractFixedField K Ω H)) :=
    abstractExtensionQuotientEquivGaloisGroup K Ω H U hUH hUnormal
    (QuotientGroup.mk σ)
  have hc := AlgEquiv.restrictNormal_commutes τ (abstractFixedField K Ω J) x
  have hval := congrArg (fun y : abstractFixedField K Ω U => (y : Ω)) hc
  change ((AlgEquiv.restrictNormalHom (abstractFixedField K Ω J) τ x :
      abstractFixedField K Ω J) : Ω) = _ at hval
  exact hval.trans
    ((abstractExtensionQuotientEquivGaloisGroup_mk_apply_val K Ω H U hUH hUnormal σ
      (algebraMap (abstractFixedField K Ω J) (abstractFixedField K Ω U) x)).symm.trans
        (abstractExtensionQuotientEquivGaloisGroup_mk_apply_val K Ω H J hJH hJnormal σ x))

/-- The actual restriction map agrees with restriction of the abstract quotient. -/
theorem abstractFixedField_restrictNormal_quotient
    (H J U : ClosedSubgroup Gal(Ω/K))
    (hJH : J.toSubgroup ≤ H.toSubgroup) (hUH : U.toSubgroup ≤ H.toSubgroup)
    (hUJ : U.toSubgroup ≤ J.toSubgroup)
    (hJnormal : (extensionSubgroup H J hJH).Normal)
    (hUnormal : (extensionSubgroup H U hUH).Normal) :
    let _ := hJnormal
    let _ := hUnormal
    let _ : Algebra (abstractFixedField K Ω H) (abstractFixedField K Ω J) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω hJH)).toRingHom.toAlgebra
    let _ : Algebra (abstractFixedField K Ω H) (abstractFixedField K Ω U) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω hUH)).toRingHom.toAlgebra
    let _ : Algebra (abstractFixedField K Ω J) (abstractFixedField K Ω U) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω hUJ)).toRingHom.toAlgebra
    let _ : IsScalarTower (abstractFixedField K Ω H) (abstractFixedField K Ω J)
        (abstractFixedField K Ω U) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : IsGalois (abstractFixedField K Ω H) (abstractFixedField K Ω J) :=
      abstractRelativeFixedField_isGalois K Ω H J hJH hJnormal
    ∀ q : H.toSubgroup ⧸ extensionSubgroup H U hUH,
      AlgEquiv.restrictNormalHom (F := abstractFixedField K Ω H)
          (K₁ := abstractFixedField K Ω U) (abstractFixedField K Ω J)
          (abstractExtensionQuotientEquivGaloisGroup K Ω H U hUH hUnormal q) =
        abstractExtensionQuotientEquivGaloisGroup K Ω H J hJH hJnormal
          (finiteReciprocityNaturalityRestriction H H J U hJH hUH le_rfl hUJ q) := by
  intro hnJ hnU aFJ aFU aJU hFJU hgal q
  refine QuotientGroup.induction_on q ?_
  intro σ
  exact abstractFixedField_restrictNormal_quotient_mk K Ω H J U hJH hUH hUJ hJnormal hUnormal σ

/-- The same comparison holds after passing to abelianized Galois groups. -/
theorem abstractFixedField_restrictNormal_abelianization
    (H J U : ClosedSubgroup Gal(Ω/K))
    (hJH : J.toSubgroup ≤ H.toSubgroup) (hUH : U.toSubgroup ≤ H.toSubgroup)
    (hUJ : U.toSubgroup ≤ J.toSubgroup)
    (hJnormal : (extensionSubgroup H J hJH).Normal)
    (hUnormal : (extensionSubgroup H U hUH).Normal) :
    let _ := hJnormal
    let _ := hUnormal
    let _ : Algebra (abstractFixedField K Ω H) (abstractFixedField K Ω J) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω hJH)).toRingHom.toAlgebra
    let _ : Algebra (abstractFixedField K Ω H) (abstractFixedField K Ω U) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω hUH)).toRingHom.toAlgebra
    let _ : Algebra (abstractFixedField K Ω J) (abstractFixedField K Ω U) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω hUJ)).toRingHom.toAlgebra
    let _ : IsScalarTower (abstractFixedField K Ω H) (abstractFixedField K Ω J)
        (abstractFixedField K Ω U) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : IsGalois (abstractFixedField K Ω H) (abstractFixedField K Ω J) :=
      abstractRelativeFixedField_isGalois K Ω H J hJH hJnormal
    ∀ z : Abelianization (H.toSubgroup ⧸ extensionSubgroup H U hUH),
      Abelianization.map
          (AlgEquiv.restrictNormalHom (F := abstractFixedField K Ω H)
          (K₁ := abstractFixedField K Ω U) (abstractFixedField K Ω J))
          ((abstractExtensionQuotientEquivGaloisGroup K Ω H U hUH hUnormal).abelianizationCongr z) =
        (abstractExtensionQuotientEquivGaloisGroup K Ω H J hJH hJnormal).abelianizationCongr
          (Abelianization.map
            (finiteReciprocityNaturalityRestriction H H J U hJH hUH le_rfl hUJ) z) := by
  intro hnJ hnU aFJ aFU aJU hFJU hgal z
  refine QuotientGroup.induction_on z ?_
  intro q
  change Abelianization.of
      ((AlgEquiv.restrictNormalHom (F := abstractFixedField K Ω H)
          (K₁ := abstractFixedField K Ω U) (abstractFixedField K Ω J))
        (abstractExtensionQuotientEquivGaloisGroup K Ω H U hUH hUnormal q)) =
    Abelianization.of (abstractExtensionQuotientEquivGaloisGroup K Ω H J hJH hJnormal
      (finiteReciprocityNaturalityRestriction H H J U hJH hUH le_rfl hUJ q))
  exact congrArg Abelianization.of
    (abstractFixedField_restrictNormal_quotient K Ω H J U
      hJH hUH hUJ hJnormal hUnormal q)

end FunctionField

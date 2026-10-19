/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.Main
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.NormComparison
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.Representation
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.ClassFormation.Valuation
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.ClassGroupNorm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormIsomorphism
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits

/-!
# Norm compatibility for actual fixed-field Artin symbols

In one common Galois closure, the Artin symbol of the actual idele-class
norm is the upper Artin automorphism regarded over the lower base field.
The abstract norm-restriction theorem supplies the reciprocity square;
the actual norm comparison and ambient automorphism representatives identify
both vertical maps. Comparing symbols constructed from different ambient
class formations is a separate assertion.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

private theorem abstractFixedField_restrictScalars_abelianization
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (H J U : ClosedSubgroup Gal(Ω/K))
    (hJH : J.toSubgroup ≤ H.toSubgroup)
    (hUH : U.toSubgroup ≤ H.toSubgroup)
    (hUJ : U.toSubgroup ≤ J.toSubgroup)
    [hUnormal : (extensionSubgroup H U hUH).Normal]
    [hU'normal : (extensionSubgroup J U hUJ).Normal] :
    let _ : Algebra (abstractFixedField K Ω H) (abstractFixedField K Ω J) :=
      (abstractRelativeFixedField K Ω hJH).algebra
    let _ : Algebra (abstractFixedField K Ω H) (abstractFixedField K Ω U) :=
      (abstractRelativeFixedField K Ω hUH).algebra
    let _ : Algebra (abstractFixedField K Ω J) (abstractFixedField K Ω U) :=
      (abstractRelativeFixedField K Ω hUJ).algebra
    let _ : IsScalarTower (abstractFixedField K Ω H) (abstractFixedField K Ω J)
        (abstractFixedField K Ω U) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let eJU : (J.toSubgroup ⧸ extensionSubgroup J U hUJ) ≃*
        Gal((abstractFixedField K Ω U)/(abstractFixedField K Ω J)) :=
      abstractExtensionQuotientEquivGaloisGroup K Ω J U hUJ hU'normal
    let eHU : (H.toSubgroup ⧸ extensionSubgroup H U hUH) ≃*
        Gal((abstractFixedField K Ω U)/(abstractFixedField K Ω H)) :=
      abstractExtensionQuotientEquivGaloisGroup K Ω H U hUH hUnormal
    ∀ z : Abelianization (J.toSubgroup ⧸ extensionSubgroup J U hUJ),
      Abelianization.map (AlgEquiv.restrictScalarsHom (abstractFixedField K Ω H))
          (eJU.abelianizationCongr z) =
        eHU.abelianizationCongr
            (normResidueNaturalityAbelianizedRestriction H J U U
              hUH hUJ hJH le_rfl z) := by
  intro aFJ aFU aJU hFJU eJU eHU z
  refine QuotientGroup.induction_on z ?_
  intro q
  refine QuotientGroup.induction_on q ?_
  intro σ
  change Abelianization.of
      ((eJU (QuotientGroup.mk σ)).restrictScalars (abstractFixedField K Ω H)) =
    Abelianization.of (eHU (QuotientGroup.mk (Subgroup.inclusion hJH σ)))
  apply congrArg Abelianization.of
  apply AlgEquiv.ext
  intro x
  apply Subtype.val_injective
  exact (abstractExtensionQuotientEquivGaloisGroup_mk_apply_val K Ω J U
    hUJ hU'normal σ x).symm.trans
      (abstractExtensionQuotientEquivGaloisGroup_mk_apply_val K Ω H U
        hUH hUnormal (Subgroup.inclusion hJH σ) x)

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω] [IsSepClosed Ω]

/-- Norming an actual fixed-field idele class restricts the scalars of its Artin automorphism. -/
theorem fixedFieldArtin_norm_restrictScalars
    (T : FiniteAbstractFieldExtension Gal(Ω/K)) (U : ClosedSubgroup Gal(Ω/K))
    (hUH : U.toSubgroup ≤ T.base.field.toSubgroup)
    (hUJ : U.toSubgroup ≤ T.field.field.toSubgroup)
    (hJnormal : (extensionSubgroup T.base.field T.field.field T.below).Normal)
    [hUnormal : (extensionSubgroup T.base.field U hUH).Normal]
    [hU'normal : (extensionSubgroup T.field.field U hUJ).Normal]
    [hUfinite : Finite (T.base.field.toSubgroup ⧸
      extensionSubgroup T.base.field U hUH)]
    [hU'finite : Finite (T.field.field.toSubgroup ⧸
      extensionSubgroup T.field.field U hUJ)] :
    let _ : FiniteDimensional K (abstractFixedField K Ω T.base.field) :=
      abstractFixedField_finiteDimensional K Ω T.base.field T.base.finite
    let _ : FiniteDimensional K (abstractFixedField K Ω T.field.field) :=
      abstractFixedField_finiteDimensional K Ω T.field.field T.field.finite
    let _ : Algebra (abstractFixedField K Ω T.base.field)
        (abstractFixedField K Ω T.field.field) :=
      (abstractRelativeFixedField K Ω T.below).algebra
    let _ : Algebra (abstractFixedField K Ω T.base.field) (abstractFixedField K Ω U) :=
      (abstractRelativeFixedField K Ω hUH).algebra
    let _ : Algebra (abstractFixedField K Ω T.field.field) (abstractFixedField K Ω U) :=
      (abstractRelativeFixedField K Ω hUJ).algebra
    let _ : IsScalarTower (abstractFixedField K Ω T.base.field)
        (abstractFixedField K Ω T.field.field) (abstractFixedField K Ω U) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : IsScalarTower K (abstractFixedField K Ω T.base.field)
        (abstractFixedField K Ω T.field.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : IsScalarTower k (abstractFixedField K Ω T.base.field)
        (abstractFixedField K Ω T.field.field) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let _ : FiniteDimensional (abstractFixedField K Ω T.base.field)
        (abstractFixedField K Ω T.field.field) := FiniteDimensional.right K _ _
    let _ : IsGalois (abstractFixedField K Ω T.base.field)
        (abstractFixedField K Ω T.field.field) :=
      abstractRelativeFixedField_isGalois K Ω T.base.field T.field.field T.below hJnormal
    ∀ c : IdeleClassGroup k (abstractFixedField K Ω T.field.field),
      Abelianization.map
        (AlgEquiv.restrictScalarsHom (abstractFixedField K Ω T.base.field) :
          Gal((abstractFixedField K Ω U)/(abstractFixedField K Ω T.field.field)) →*
          Gal((abstractFixedField K Ω U)/(abstractFixedField K Ω T.base.field)))
          (fixedFieldArtin k K Ω T.field ⟨U, hUJ, hU'normal, hU'finite⟩ c) =
        fixedFieldArtin k K Ω T.base ⟨U, hUH, hUnormal, hUfinite⟩
          (IdeleClassGroup.norm (k := k) (K := abstractFixedField K Ω T.base.field)
            (L := abstractFixedField K Ω T.field.field) c) := by
  intro hFfinite hEfinite aFE aFU aEU hFEU hKFE hkFE hFEfinite hFEgal c
  let A := ideleClassRepresentation k K Ω
  let D := fullConstantDegreeData k K Ω
  let v := ideleClassValuationData k K Ω
  have hcf := ideleClassRepresentation_satisfiesClassFieldAxiom k K Ω
  let E : FiniteGaloisSubextension T.base.field := ⟨U, hUH, hUnormal, hUfinite⟩
  let E' : FiniteGaloisSubextension T.field.field := ⟨U, hUJ, hU'normal, hU'finite⟩
  let eG : E.extensionQuotient ≃*
      Gal((abstractFixedField K Ω U)/(abstractFixedField K Ω T.base.field)) :=
    abstractExtensionQuotientEquivGaloisGroup K Ω T.base.field U hUH hUnormal
  let eG' : E'.extensionQuotient ≃*
      Gal((abstractFixedField K Ω U)/(abstractFixedField K Ω T.field.field)) :=
    abstractExtensionQuotientEquivGaloisGroup K Ω T.field.field U hUJ hU'normal
  let a := abstractFixedClassEquiv k K Ω T.field.field T.field.finite (Additive.ofMul c)
  let z := ((D.normResidueSymbol A v hcf T.field E')
    (finiteNormClass A T.field.field U hUJ a)).toMul
  have hg :
      Abelianization.map
        (AlgEquiv.restrictScalarsHom (abstractFixedField K Ω T.base.field) :
          Gal((abstractFixedField K Ω U)/(abstractFixedField K Ω T.field.field)) →*
          Gal((abstractFixedField K Ω U)/(abstractFixedField K Ω T.base.field)))
          (eG'.abelianizationCongr z) =
        eG.abelianizationCongr
          (normResidueNaturalityAbelianizedRestriction T.base.field T.field.field U U
            hUH hUJ T.below le_rfl z) :=
    abstractFixedField_restrictScalars_abelianization K Ω
      T.base.field T.field.field U T.below hUH hUJ z
  have h := DFunLike.congr_fun
    (D.normResidueNaturality_norm_restriction A v hcf T U U hUH hUJ le_rfl)
    (finiteNormClass A T.field.field U hUJ a)
  change Additive.ofMul
      (normResidueNaturalityAbelianizedRestriction T.base.field T.field.field U U
        hUH hUJ T.below le_rfl z) =
    (D.normResidueSymbol A v hcf T.base E)
      (finiteReciprocityNaturalityNormMap A T.base.field T.field.field U U
        hUH hUJ T.below le_rfl (finiteNormClass A T.field.field U hUJ a)) at h
  have hq := finiteReciprocityNaturalityNormMap_finiteNormClass A
    T.base.field T.field.field U U hUH hUJ T.below le_rfl a
  have hN := abstractFixedClassEquiv_norm k K Ω T.base T.field T.below
    hJnormal (Additive.ofMul c)
  have hclass := hq.trans
    (congrArg (finiteNormClass A T.base.field U hUH) hN.symm)
  have hsymbol := h.trans
    (congrArg (D.normResidueSymbol A v hcf T.base E) hclass)
  change Abelianization.map
        (AlgEquiv.restrictScalarsHom (abstractFixedField K Ω T.base.field) :
          Gal((abstractFixedField K Ω U)/(abstractFixedField K Ω T.field.field)) →*
          Gal((abstractFixedField K Ω U)/(abstractFixedField K Ω T.base.field)))
      (eG'.abelianizationCongr z) =
    eG.abelianizationCongr
        ((D.normResidueSymbol A v hcf T.base E)
          (finiteNormClass A T.base.field U hUH
            (abstractFixedClassEquiv k K Ω T.base.field T.base.finite
              (Additive.ofMul (IdeleClassGroup.norm (k := k)
                (K := abstractFixedField K Ω T.base.field)
                (L := abstractFixedField K Ω T.field.field) c))))).toMul
  exact hg.trans (congrArg eG.abelianizationCongr (congrArg Additive.toMul hsymbol))

/-- Ambient norm reciprocity descends through an actual degree-one base presentation. -/
theorem fixedFieldArtin_norm_of_basePresentation
    (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [AlgebraicCurve.HasPrincipalDivisors k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsGalois K Ω] [IsSepClosed Ω]
    (B₀ H₀ : FiniteAbstractField Gal(Ω/K))
    (hHB : H₀.field.toSubgroup ≤ B₀.field.toSubgroup)
    [hHfinite : Finite (B₀.field.toSubgroup ⧸ extensionSubgroup B₀.field H₀.field hHB)]
    (U : ClosedSubgroup Gal(Ω/K))
    (hUB : U.toSubgroup ≤ B₀.field.toSubgroup)
    (hUH : U.toSubgroup ≤ H₀.field.toSubgroup)
    (hHnormal : (extensionSubgroup B₀.field H₀.field hHB).Normal)
    [H₀.field.toSubgroup.Normal]
    [hUnormal : (extensionSubgroup B₀.field U hUB).Normal]
    [hU'normal : (extensionSubgroup H₀.field U hUH).Normal]
    [hUfinite : Finite (B₀.field.toSubgroup ⧸
      extensionSubgroup B₀.field U hUB)]
    [hU'finite : Finite (H₀.field.toSubgroup ⧸
      extensionSubgroup H₀.field U hUH)]
    (eB : K ≃ₐ[K] abstractFixedField K Ω B₀.field) :
    let _ : CommSemiring (abstractFixedField K Ω U) :=
      (inferInstance : Field (abstractFixedField K Ω U)).toSemifield.toCommSemiring
    let aKU : Algebra K (abstractFixedField K Ω U) :=
      IntermediateField.algebra' (R' := K) (abstractFixedField K Ω U)
    let _ : SMul K (abstractFixedField K Ω U) := aKU.toSMul
    let aBE : Algebra (abstractFixedField K Ω B₀.field) (abstractFixedField K Ω U) :=
      (abstractRelativeFixedField K Ω hUB).algebra
    let _ : SMul (abstractFixedField K Ω B₀.field) (abstractFixedField K Ω U) := aBE.toSMul
    let aHE : Algebra (abstractFixedField K Ω H₀.field) (abstractFixedField K Ω U) :=
      (abstractRelativeFixedField K Ω hUH).algebra
    let _ : SMul (abstractFixedField K Ω H₀.field) (abstractFixedField K Ω U) := aHE.toSMul
    have _ : FiniteDimensional K (abstractFixedField K Ω B₀.field) :=
      abstractFixedField_finiteDimensional K Ω B₀.field B₀.finite
    have _ : FiniteDimensional K (abstractFixedField K Ω H₀.field) :=
      abstractFixedField_finiteDimensional K Ω H₀.field H₀.finite
    have _ : IsGalois K (abstractFixedField K Ω B₀.field) :=
      IsGalois.of_algEquiv eB
    have _ : IsGalois K (abstractFixedField K Ω H₀.field) :=
      IsGalois.of_fixedField_normal_subgroup H₀.field.toSubgroup
    have _ : IsScalarTower K (abstractFixedField K Ω B₀.field)
        (abstractFixedField K Ω U) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    have _ : IsScalarTower K (abstractFixedField K Ω H₀.field)
        (abstractFixedField K Ω U) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    ∀ c : IdeleClassGroup k (abstractFixedField K Ω H₀.field),
      let n : IdeleClassGroup k K := IdeleClassGroup.norm (k := k) (K := K)
        (L := abstractFixedField K Ω H₀.field) c
      Abelianization.map
        (AlgEquiv.restrictScalarsHom
          (S := abstractFixedField K Ω B₀.field)
          (A := abstractFixedField K Ω U) K :
          Gal((abstractFixedField K Ω U)/(abstractFixedField K Ω B₀.field)) →*
          Gal((abstractFixedField K Ω U)/K))
        (fixedFieldArtin k K Ω B₀ ⟨U, hUB, hUnormal, hUfinite⟩
          (IdeleClassGroup.baseChange (k := k) (K := K)
            (L := abstractFixedField K Ω B₀.field) n)) =
      Abelianization.map
        (AlgEquiv.restrictScalarsHom
          (S := abstractFixedField K Ω H₀.field)
          (A := abstractFixedField K Ω U) K :
          Gal((abstractFixedField K Ω U)/(abstractFixedField K Ω H₀.field)) →*
          Gal((abstractFixedField K Ω U)/K))
        (fixedFieldArtin k K Ω H₀ ⟨U, hUH, hU'normal, hU'finite⟩ c) := by
  intro cU aKU sKU aBE sBE aHE sHE hKBfinite hKHfinite hKBgal hKHgal hKBE hKHE c n
  let B := abstractFixedField K Ω B₀.field
  let H := abstractFixedField K Ω H₀.field
  let E := abstractFixedField K Ω U
  let aBH : Algebra B H := (abstractRelativeFixedField K Ω hHB).algebra
  let _ : SMul B H := aBH.toSMul
  let _ : Module B H := aBH.toModule
  change IsScalarTower K B E at hKBE
  change IsScalarTower K H E at hKHE
  have hKBH : IsScalarTower K B H :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hkBH : IsScalarTower k B H :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hBHE : IsScalarTower B H E :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hBHfinite : FiniteDimensional B H := FiniteDimensional.right K B H
  have hBHgal : IsGalois B H := IsGalois.tower_top_of_isGalois K B H
  have hB : Module.finrank K B = 1 := by
    rw [← eB.toLinearEquiv.finrank_eq, Module.finrank_self]
  have hnorm := IdeleClassGroup.baseChange_norm_of_base_finrank_one
    (k := k) (K := K) (F := B) (L := H) hB c
  let X : FiniteAbstractFieldExtension Gal(Ω/K) := ⟨H₀, B₀, hHB, hHfinite⟩
  let ρ0 : Gal(E/B) →* Gal(E/K) := AlgEquiv.restrictScalarsHom K
  let ρH : Gal(E/H) →* Gal(E/B) := AlgEquiv.restrictScalarsHom B
  let ρ : Gal(E/H) →* Gal(E/K) := AlgEquiv.restrictScalarsHom K
  have hambient :
      Abelianization.map ρH
          (fixedFieldArtin k K Ω H₀ ⟨U, hUH, hU'normal, hU'finite⟩ c) =
        fixedFieldArtin k K Ω B₀ ⟨U, hUB, hUnormal, hUfinite⟩
          (IdeleClassGroup.norm (k := k) (K := B) (L := H) c) := by
    with_reducible_and_instances
      exact fixedFieldArtin_norm_restrictScalars k K Ω X U hUB hUH hHnormal c
  rw [← hnorm] at hambient
  have hcomp : ρ0.comp ρH = ρ := by
    apply MonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    rfl
  have hrestrict : (Abelianization.map ρ0).comp (Abelianization.map ρH) =
      Abelianization.map ρ :=
    (Abelianization.map_comp ρH ρ0).trans (congrArg Abelianization.map hcomp)
  have htransport := congrArg (Abelianization.map ρ0) hambient.symm
  refine htransport.trans ?_
  exact DFunLike.congr_fun hrestrict _

end FunctionField

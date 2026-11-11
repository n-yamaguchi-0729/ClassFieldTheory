/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Abelian.FiniteTransferSquare
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FixedFieldAbsoluteArtin
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.NativeFixedFieldArtinTransfer
public import Nyll.ClassFieldTheory.Algebra.GaloisRestrictionFinrankOne
public import Nyll.ProCGroups.GroupTheory.MonoidHomMapTransferEqTransferComp
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup

/-!
# Original finite transfer on absolute Galois representatives

The intrinsic base is the whole original absolute Galois group. Its
quotient-to-fixed-field equivalence acts on field elements by the original
automorphism. These literal formulas identify native finite transfer with
the transfer of the actual finite restriction character of the ambient
subgroup. No Artin symbol is used in this group comparison.
-/

@[expose] public section

universe v w

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory ProCGroups.Abelian
open KummerTheory CyclicCohomology
open ProCGroups.FiniteStepSolvableQuotients
open scoped IsMulCommutative

/-- The original quotient-to-Galois equivalence has the literal action of
its subgroup representative on the relative fixed field. -/
theorem fixedFieldQuotientGaloisEquiv_mk_commutes
    (K : Type v) (Ω : Type w) [Field K] [Field Ω]
    [Algebra K Ω] [IsGalois K Ω]
    (H T : ClosedSubgroup Gal(Ω/K)) (hT : T.toSubgroup ≤ H.toSubgroup)
    [hNormal : (extensionSubgroup H T hT).Normal]
    (σ : H.toSubgroup) (x : abstractRelativeFixedField K Ω hT) :
    algebraMap (abstractRelativeFixedField K Ω hT) Ω
        (abstractExtensionQuotientEquivGaloisGroup K Ω H T hT hNormal
          (QuotientGroup.mk σ) x) =
      σ.val (algebraMap (abstractRelativeFixedField K Ω hT) Ω x) := by
  let F := abstractFixedField K Ω H
  let E := abstractRelativeFixedField K Ω hT
  have hgalΩ : IsGalois F Ω := IsGalois.tower_top_of_isGalois K F Ω
  have hfix : E.fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal K Ω H T hT hNormal
  let J : ClosedSubgroup Gal(Ω/F) := RamificationTheory.closedFixingSubgroup F Ω E
  have hJnormal : J.toSubgroup.Normal := hfix
  have hJgalois : IsGalois F (IntermediateField.fixedField J.toSubgroup) :=
    IsGalois.of_fixedField_normal_subgroup J.toSubgroup
  let eE := IntermediateField.equivOfEq (InfiniteGalois.fixedField_fixingSubgroup E)
  change algebraMap (IntermediateField.fixedField J.toSubgroup) Ω
      ((AlgEquiv.restrictNormalHom (IntermediateField.fixedField J.toSubgroup)
        (abstractSubgroupEquivGaloisGroup K Ω H σ)) (eE.symm x)) = _
  exact AlgEquiv.restrictNormal_commutes (abstractSubgroupEquivGaloisGroup K Ω H σ)
    (IntermediateField.fixedField J.toSubgroup) (eE.symm x)

private theorem fixedFieldQuotientGaloisEquiv_mk_restrictScalars
    (K : Type v) (Ω : Type w) [Field K] [Field Ω]
    [Algebra K Ω] [IsGalois K Ω]
    (H T : ClosedSubgroup Gal(Ω/K)) (hT : T.toSubgroup ≤ H.toSubgroup)
    [hNormal : (extensionSubgroup H T hT).Normal] [T.toSubgroup.Normal]
    (σ : H.toSubgroup) :
    let F := abstractFixedField K Ω H
    let E := abstractFixedField K Ω T
    let _ : Algebra F E := (abstractRelativeFixedField K Ω hT).algebra
    have _ : IsScalarTower K F E :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    have _ : IsGalois K E := IsGalois.of_fixedField_normal_subgroup T.toSubgroup
    let e : (H.toSubgroup ⧸ extensionSubgroup H T hT) ≃* Gal(E/F) :=
      abstractExtensionQuotientEquivGaloisGroup K Ω H T hT hNormal
    (e (QuotientGroup.mk σ)).restrictScalars K = AlgEquiv.restrictNormalHom E σ.val := by
  intro F E aFE hKFE hEgal e
  apply AlgEquiv.ext
  intro x
  apply (algebraMap E Ω).injective
  exact (fixedFieldQuotientGaloisEquiv_mk_commutes K Ω H T hT σ x).trans
    (AlgEquiv.restrictNormal_commutes σ.val E x).symm

private theorem fixedFieldQuotientGaloisEquiv_mk_restriction
    (K : Type v) (Ω : Type w) [Field K] [Field Ω]
    [Algebra K Ω] [IsGalois K Ω]
    (H : FiniteAbstractField Gal(Ω/K)) (T : FiniteGaloisSubextension H.field)
    (σ : H.field.toSubgroup) :
    abstractExtensionQuotientEquivGaloisGroup K Ω H.field T.field T.below T.normal
        (QuotientGroup.mk σ) = fixedFieldSubgroupFiniteRestriction K Ω H T σ := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap (abstractRelativeFixedField K Ω T.below) Ω).injective
  exact (fixedFieldQuotientGaloisEquiv_mk_commutes K Ω H.field T.field T.below σ x).trans
    (fixedFieldSubgroupFiniteRestriction_commutes K Ω H T σ x).symm

/-- The subgroup of the intrinsic abstract base is the original whole
absolute Galois group, through its literal subgroup inclusion. -/
def intrinsicBaseSubgroupEquiv (K : Type v) [Field K] :
    Gal(SeparableClosure K/K) ≃* (intrinsicFiniteAbstractBase K).field.toSubgroup where
  toFun σ := ⟨σ, by
    rw [congrArg FiniteAbstractField.field (intrinsicFiniteAbstractBase_eq_base K)]
    exact Subgroup.mem_top σ⟩
  invFun σ := σ.val
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

/-- A finite normal original fixed subgroup is an actual open normal subgroup. -/
@[reducible] def finiteAbstractOpenNormal
    (K : Type v) (Ω : Type w) [Field K] [Field Ω]
    [Algebra K Ω] [IsGalois K Ω]
    (H : FiniteAbstractField Gal(Ω/K)) [H.field.toSubgroup.Normal] :
    OpenNormalSubgroup Gal(Ω/K) where
  toSubgroup := H.field.toSubgroup
  isOpen' := abstractFiniteClosedSubgroup_isOpen K Ω H.field H.finite
  isNormal' := inferInstance

private theorem transfer_character_via_abelianizations
    {P Q R A B C : Type*} [Group P] [Group Q] [Group R]
    [Group A] [Group B] [Group C]
    (q : P →* Q) (hq : Function.Surjective q)
    (H : Subgroup P) [H.FiniteIndex] (hker : q.ker ≤ H)
    (J : Subgroup Q) [J.FiniteIndex]
    (r : H →* R) (hr : Function.Surjective r) (e : R ≃* J)
    (hsquare : ∀ h : H, (e (r h)).val = q h.val)
    (eB : Q ≃* A) (e₀ : A ≃* B) (eH : R ≃* C)
    (p : P) (τ : B) (hsource : e₀ (eB (q p)) = τ) :
    eH.abelianizationCongr
        (e.symm.abelianizationCongr
          (Abelianization.lift
            (MonoidHom.transfer (Abelianization.of : J →* Abelianization J))
            (eB.abelianizationCongr.symm
              (e₀.abelianizationCongr.symm (Abelianization.of τ))))) =
      MonoidHom.transfer
        ((Abelianization.of.comp eH.toMonoidHom).comp r) p := by
  have hsourceAb : eB.abelianizationCongr.symm
      (e₀.abelianizationCongr.symm (Abelianization.of τ)) =
        Abelianization.of (q p) := by
    apply eB.abelianizationCongr.injective
    rw [eB.abelianizationCongr.apply_symm_apply]
    apply e₀.abelianizationCongr.injective
    rw [e₀.abelianizationCongr.apply_symm_apply]
    exact congrArg Abelianization.of hsource.symm
  let χ : R →* Abelianization C := Abelianization.of.comp eH.toMonoidHom
  let β : Abelianization J →* Abelianization C :=
    eH.abelianizationCongr.toMonoidHom.comp e.symm.abelianizationCongr.toMonoidHom
  have hβ : β.comp (Abelianization.of : J →* Abelianization J) =
      χ.comp e.symm.toMonoidHom := by
    apply MonoidHom.ext
    intro j
    rfl
  rw [hsourceAb]
  change β (MonoidHom.transfer (Abelianization.of : J →* Abelianization J) (q p)) = _
  rw [MonoidHom.map_transfer_eq_transfer_comp, hβ]
  exact (transfer_character_through_range_equiv
    q hq H hker J r hr e hsquare χ p).symm

section Transfer

variable (K : Type v) [Field K]
    (H : FiniteAbstractField Gal(SeparableClosure K/K))
    (T : FiniteGaloisSubextension H.field) [T.field.toSubgroup.Normal]

/-- The native finite transfer, evaluated on an original absolute
automorphism, is the ordinary transfer of the original subgroup's actual
finite restriction character. The lower finite quotient may be nonabelian. -/
theorem nativeFixedFieldAbelianizedTransfer_restrict
    (σ : Gal(SeparableClosure K/K)) :
    have _ : FiniteDimensional K (abstractFixedField K (SeparableClosure K) T.field) :=
      abstractFixedField_finiteDimensional K (SeparableClosure K) T.field
        T.toFiniteAbstractFieldExtension.field.finite
    have _ : IsGalois K (abstractFixedField K (SeparableClosure K) T.field) :=
      IsGalois.of_fixedField_normal_subgroup T.field.toSubgroup
    have _ : Finite (Gal(SeparableClosure K/K) ⧸ H.field.toSubgroup) :=
      ambientQuotientFiniteOfAbstractFinite K (SeparableClosure K) H.field H.finite
    have _ : H.field.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    nativeFixedFieldAbelianizedTransfer K H T
        (Abelianization.of
          (AlgEquiv.restrictNormalHom (abstractFixedField K (SeparableClosure K) T.field) σ)) =
      MonoidHom.transfer
        (Abelianization.of.comp
          (fixedFieldSubgroupFiniteRestriction K (SeparableClosure K) H T).toMonoidHom) σ := by
  intro hEfinite hEgal hHfinite hHindex
  let Ω := SeparableClosure K
  let B := intrinsicFiniteAbstractBase K
  let F₀ := abstractFixedField K Ω B.field
  let E := abstractFixedField K Ω T.field
  let b := intrinsicBaseSubgroupEquiv K
  have hB : B.field = baseField Gal(Ω/K) :=
    congrArg FiniteAbstractField.field (intrinsicFiniteAbstractBase_eq_base K)
  have hHB : H.field.toSubgroup ≤ B.field.toSubgroup := by
    rw [hB]
    exact le_baseField H.field
  have hTB : T.field.toSubgroup ≤ B.field.toSubgroup := T.below.trans hHB
  have hNormal : (extensionSubgroup B.field T.field hTB).Normal := by infer_instance
  have hFinite : Finite (B.field.toSubgroup ⧸ extensionSubgroup B.field T.field hTB) :=
    (finiteAbstractFieldOverIntrinsicBase K T.toFiniteAbstractFieldExtension.field).finiteQuotient
  let Q := B.field.toSubgroup ⧸ extensionSubgroup B.field T.field hTB
  let R := H.field.toSubgroup ⧸ extensionSubgroup H.field T.field T.below
  let q : Gal(Ω/K) →* Q :=
    (QuotientGroup.mk' (extensionSubgroup B.field T.field hTB)).comp b.toMonoidHom
  let r : H.field.toSubgroup →* R :=
    QuotientGroup.mk' (extensionSubgroup H.field T.field T.below)
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective _).comp b.surjective
  have hr : Function.Surjective r := QuotientGroup.mk'_surjective _
  have hker : q.ker ≤ H.field.toSubgroup := by
    intro τ hτ
    have hmem : b τ ∈ extensionSubgroup B.field T.field hTB :=
      (QuotientGroup.eq_one_iff (b τ)).mp hτ
    exact T.below ((mem_extensionSubgroup_iff B.field T.field hTB (b τ)).mp hmem)
  let J := transferNormNaturalityIntermediateSubgroup B.field H.field T.field T.below hHB
  have hJindex : J.FiniteIndex := Subgroup.finiteIndex_of_finite
  let e := transferNormNaturalityIntermediateQuotientEquiv
    B.field H.field T.field T.below hHB
  have hsquare (h : H.field.toSubgroup) : (e (r h)).val = q h.val := rfl
  let aF₀E : Algebra F₀ E := (abstractRelativeFixedField K Ω hTB).algebra
  have hKF₀E : IsScalarTower K F₀ E :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hF₀ : Module.finrank K F₀ = 1 := by
    rw [← (finiteGaloisBaseFixedFieldEquiv K).toLinearEquiv.finrank_eq,
      Module.finrank_self]
  let e₀ : Gal(E/F₀) ≃* Gal(E/K) :=
    ClassFieldTheory.galoisRestrictScalarsEquivOfFinrankOne hF₀
  let eB : Q ≃* Gal(E/F₀) := abstractExtensionQuotientEquivGaloisGroup
    K Ω B.field T.field hTB hNormal
  let eH := abstractExtensionQuotientEquivGaloisGroup
    K Ω H.field T.field T.below T.normal
  have hsource : e₀ (eB (q σ)) = AlgEquiv.restrictNormalHom E σ :=
    fixedFieldQuotientGaloisEquiv_mk_restrictScalars K Ω B.field T.field hTB (b σ)
  let χ : R →* Abelianization
      Gal((abstractRelativeFixedField K Ω T.below)/(abstractFixedField K Ω H.field)) :=
    Abelianization.of.comp eH.toMonoidHom
  have hcharacter : χ.comp r = Abelianization.of.comp
      (fixedFieldSubgroupFiniteRestriction K Ω H T).toMonoidHom := by
    apply MonoidHom.ext
    intro h
    exact congrArg Abelianization.of
      (fixedFieldQuotientGaloisEquiv_mk_restriction K Ω H T h)
  have hgroup := transfer_character_via_abelianizations
    q hq H.field.toSubgroup hker J r hr e hsquare eB e₀ eH σ
    (AlgEquiv.restrictNormalHom E σ) hsource
  change eH.abelianizationCongr
    (transferNormNaturalityTransfer B.field H.field T.field T.below hHB
      (eB.abelianizationCongr.symm
        (e₀.abelianizationCongr.symm (Abelianization.of (AlgEquiv.restrictNormalHom E σ))))) = _
  exact hgroup.trans
    (congrArg
      (fun ψ : H.field.toSubgroup →* Abelianization
          Gal((abstractRelativeFixedField K Ω T.below)/(abstractFixedField K Ω H.field)) =>
        MonoidHom.transfer ψ σ) hcharacter)

variable [H.field.toSubgroup.Normal] [IsMulCommutative T.extensionQuotient]

/-- Every actual relative abelian fixed-field coordinate of the original
topological transfer is the native finite transfer of the original
absolute finite Galois abelianization coordinate. -/
theorem nativeFixedFieldAbelianizedTransfer_absoluteCoordinate
    (z : localAbsoluteAbelianProfinite K) :
    have _ : FiniteDimensional K (abstractFixedField K (SeparableClosure K) T.field) :=
      abstractFixedField_finiteDimensional K (SeparableClosure K) T.field
        T.toFiniteAbstractFieldExtension.field.finite
    have _ : IsGalois K (abstractFixedField K (SeparableClosure K) T.field) :=
      IsGalois.of_fixedField_normal_subgroup T.field.toSubgroup
    have _ : Finite (Gal(SeparableClosure K/K) ⧸ H.field.toSubgroup) :=
      ambientQuotientFiniteOfAbstractFinite K (SeparableClosure K) H.field H.finite
    Abelianization.of
        (fixedFieldFiniteArtinProjection K (SeparableClosure K) H T
          (openNormalTransferTopologicalAbelianization
            (finiteAbstractOpenNormal K (SeparableClosure K) H) z)) =
      nativeFixedFieldAbelianizedTransfer K H T
        (absoluteAbelianizedRestriction K
          (abstractFixedField K (SeparableClosure K) T.field) z) := by
  intro hEfinite hEgal hHfinite
  have hHindex : H.field.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hrelativeFinite : FiniteDimensional (abstractFixedField K (SeparableClosure K) H.field)
      (abstractRelativeFixedField K (SeparableClosure K) T.below) :=
    abstractRelativeFixedField_finiteDimensional K (SeparableClosure K) H.field T.field
      T.below H.finite T.finite
  have hrelativeAbelian : IsAbelianGalois (abstractFixedField K (SeparableClosure K) H.field)
      (abstractRelativeFixedField K (SeparableClosure K) T.below) :=
    fixedFieldRelative_isAbelianGalois K (SeparableClosure K) H T
  refine QuotientGroup.induction_on z ?_
  intro σ
  change Abelianization.of
      (TopologicalAbelianization.lift (fixedFieldSubgroupFiniteRestriction
        K (SeparableClosure K) H T)
        (openNormalTransferTopologicalAbelianization
          (finiteAbstractOpenNormal K (SeparableClosure K) H)
          (TopologicalAbelianization.mk Gal(SeparableClosure K/K) σ))) =
    nativeFixedFieldAbelianizedTransfer K H T
      (Abelianization.of
        (AlgEquiv.restrictNormalHom (abstractFixedField K (SeparableClosure K) T.field) σ))
  have htransfer := lift_openNormalTransfer_apply_mk
    (finiteAbstractOpenNormal K (SeparableClosure K) H)
    (fixedFieldSubgroupFiniteRestriction K (SeparableClosure K) H T) σ
  calc
    _ = Abelianization.of
        (MonoidHom.transfer
          (fixedFieldSubgroupFiniteRestriction K (SeparableClosure K) H T).toMonoidHom σ) :=
      congrArg Abelianization.of htransfer
    _ = _ := by
      rw [MonoidHom.map_transfer_eq_transfer_comp]
      exact (nativeFixedFieldAbelianizedTransfer_restrict K H T σ).symm

end Transfer

end FunctionField

import GlobalClassFieldTheory.Reciprocity.GlobalNormResidueAbelianization
import GlobalClassFieldTheory.Reciprocity.GlobalNormResidueNaturality
import GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFiniteTowerNormProof

/-!
# Naturality of finite-Galois global reciprocity in abelianizations

For a finite tower `K ⊆ M ⊆ N` with `N / K` Galois, this file proves
that ordinary idèle-class norm from `M` to `K` corresponds to restriction
from `Gal(N / M)` to `Gal(N / K)`, after passing both Galois groups to their
abelianizations.  The intermediate extension `M / K` is not assumed Galois.
-/

open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open AlgebraicNumberTheory
open LocalClassFieldTheory
open KummerTheory
open CyclicCohomology

/-- Transport by an equality-induced field equivalence leaves the underlying
rational direct-limit idèle class unchanged. -/
private theorem rationalIdeleClassEquivFixed_congr_apply_val
    {A B : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ A] [FiniteDimensional ℚ B]
    (h : A = B)
    (e : B ≃ₐ[ℚ] A)
    (he : e.trans (IntermediateField.equivOfEq h) =
      (AlgEquiv.refl : B ≃ₐ[ℚ] B))
    (c : Additive (IdeleClassGroup B)) :
    ((rationalIdeleClassEquivFixed A)
        (MulEquiv.toAdditive (ideleClassCongr e) c)).1 =
      ((rationalIdeleClassEquivFixed B) c).1 := by
  cases h
  have he' : e = AlgEquiv.refl := by
    apply AlgEquiv.ext
    intro x
    have hx := DFunLike.congr_fun he x
    change e x = x at hx
    exact hx
  rw [he']
  have hc :
      MulEquiv.toAdditive
          (ideleClassCongr (AlgEquiv.refl : A ≃ₐ[ℚ] A)) c = c := by
    cases c with
    | ofMul c =>
        exact congrArg Additive.ofMul (ideleClassCongr_refl c)
  rw [hc]

section CommonTop

variable
    (K M N : Type)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field N] [NumberField N]
    [Algebra K M] [Algebra M N] [Algebra K N]
    [IsScalarTower K M N]

private theorem
    commonTopBaseIntermediateFiniteDimensional
    [FiniteDimensional K N] : FiniteDimensional K M :=
  FiniteDimensional.left K M N

omit [NumberField K] [NumberField M] [NumberField N] in
private theorem
    commonTopIntermediateTopFiniteDimensional
    [FiniteDimensional K N] : FiniteDimensional M N :=
  FiniteDimensional.right K M N

omit [NumberField K] [NumberField M] [NumberField N] in
private theorem
    commonTopIntermediateTopIsGalois
    [FiniteDimensional K N] [IsGalois K N] : IsGalois M N :=
  IsGalois.tower_top_of_isGalois K M N

/-- The two base fixing subgroups obtained from one embedding of the common
top field are nested in the direction dictated by `K ⊆ M`. -/
private theorem numberFieldEmbeddedBaseSubgroup_le_of_commonTop
    (j : N →ₐ[ℚ] SeparableClosure ℚ) :
    (numberFieldEmbeddedBaseSubgroup M N j).toSubgroup ≤
      (numberFieldEmbeddedBaseSubgroup K N j).toSubgroup := by
  change
    (numberFieldEmbeddedLowerEmbedding M N j).fieldRange.fixingSubgroup ≤
      (numberFieldEmbeddedLowerEmbedding K N j).fieldRange.fixingSubgroup
  apply
    (numberFieldEmbeddedLowerEmbedding K N j).fieldRange.fixingSubgroup_le
  intro x hx
  rcases hx with ⟨y, rfl⟩
  refine ⟨algebraMap K M y, ?_⟩
  change
    j (algebraMap M N (algebraMap K M y)) =
      j (algebraMap K N y)
  rw [IsScalarTower.algebraMap_apply K M N]

/-- In a common finite Galois overfield, the quotient between the two base
fixing subgroups is finite even when the intermediate extension is not
Galois. -/
private theorem
    numberFieldEmbeddedBaseChangeExtensionQuotient_finite_of_commonTop
    [FiniteDimensional K N] [IsGalois K N]
    (j : N →ₐ[ℚ] SeparableClosure ℚ) :
    let H := numberFieldEmbeddedBaseSubgroup K N j
    let H' := numberFieldEmbeddedBaseSubgroup M N j
    let hH'H := numberFieldEmbeddedBaseSubgroup_le_of_commonTop K M N j
    Finite
      (H.toSubgroup ⧸
        extensionSubgroup H H' hH'H) := by
  dsimp only
  let H := numberFieldEmbeddedBaseSubgroup K N j
  let H' := numberFieldEmbeddedBaseSubgroup M N j
  let J := numberFieldEmbeddedTopSubgroup K N j
  let hJH := numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j
  let hJH' : J.toSubgroup ≤ H'.toSubgroup :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup M N j
  let hH'H := numberFieldEmbeddedBaseSubgroup_le_of_commonTop K M N j
  let lower := extensionSubgroup H J hJH
  let intermediate := extensionSubgroup H H' hH'H
  have hle : lower ≤ intermediate := by
    intro sigma hsigma
    rw [mem_extensionSubgroup_iff] at hsigma ⊢
    exact hJH' hsigma
  letI : Finite (H.toSubgroup ⧸ lower) := by
    exact numberFieldEmbeddedExtensionQuotient_finite K N j
  letI : lower.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  letI : intermediate.FiniteIndex :=
    Subgroup.finiteIndex_of_le hle
  exact Subgroup.finite_quotient_of_finiteIndex

/-- The abelianized quotient of an explicitly embedded finite Galois tower
is the abelianization of its actual Galois group. -/
noncomputable def
    numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
    [FiniteDimensional K N] [IsGalois K N]
    (j : N →ₐ[ℚ] SeparableClosure ℚ) :
    Additive
        (Abelianization
          (numberFieldEmbeddedFiniteGaloisSubextension K N j).extensionQuotient) ≃+
      Additive (Abelianization Gal(N / K)) :=
  MulEquiv.toAdditive
    (MulEquiv.abelianizationCongr
      (numberFieldEmbeddedExtensionQuotientEquivGaloisGroup K N j))

/-- The finite-Galois norm-residue map built from an explicitly supplied
embedding of the top field, with target the actual Galois abelianization. -/
noncomputable def globalNormResidueAbelianizationMonoidHomOfEmbedding
    [FiniteDimensional K N] [IsGalois K N]
    (j : N →ₐ[ℚ] SeparableClosure ℚ) :
    IdeleClassGroup K →* Abelianization Gal(N / K) := by
  let e :
      (IdeleClassGroup K ⧸ (_root_.ideleClassNorm K N).range) ≃*
        Abelianization Gal(N / K) :=
    AddEquiv.toMultiplicative
      ((numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
          K N j).symm.trans
        ((rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldEmbeddedFiniteAbstractField K N j)
          (numberFieldEmbeddedFiniteGaloisSubextension K N j)).trans
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
          K N j)))
  exact e.toMonoidHom.comp
    (QuotientGroup.mk' (_root_.ideleClassNorm K N).range)

/-- Evaluation of the explicitly embedded abelianized norm-residue map on
an ordinary idèle class. -/
@[simp]
theorem globalNormResidueAbelianizationMonoidHomOfEmbedding_apply
    [FiniteDimensional K N] [IsGalois K N]
    (j : N →ₐ[ℚ] SeparableClosure ℚ)
    (c : IdeleClassGroup K) :
    letI _ : Finite
        ((numberFieldEmbeddedBaseSubgroup K N j).toSubgroup ⧸
          extensionSubgroup
            (numberFieldEmbeddedBaseSubgroup K N j)
            (numberFieldEmbeddedTopSubgroup K N j)
            (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j)) :=
      numberFieldEmbeddedExtensionQuotient_finite K N j
    globalNormResidueAbelianizationMonoidHomOfEmbedding K N j c =
      Additive.toMul
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
          K N j
          (rationalCyclotomicDegreeData.normResidueSymbol
            rationalIdeleClassRepresentation
            rationalCyclotomicIdeleClassValuationData
            rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
            (numberFieldEmbeddedFiniteAbstractField K N j)
            (numberFieldEmbeddedFiniteGaloisSubextension K N j)
            (finiteNormClass rationalIdeleClassRepresentation
              (numberFieldEmbeddedBaseSubgroup K N j)
              (numberFieldEmbeddedTopSubgroup K N j)
              (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j)
              (numberFieldEmbeddedIdeleClassEquivAmbientFixed
                K N j (Additive.ofMul c))))) := by
  dsimp only
  letI : Finite
      ((numberFieldEmbeddedBaseSubgroup K N j).toSubgroup ⧸
        extensionSubgroup
          (numberFieldEmbeddedBaseSubgroup K N j)
          (numberFieldEmbeddedTopSubgroup K N j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j)) :=
    numberFieldEmbeddedExtensionQuotient_finite K N j
  have hclass :=
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
      K N j c
  change
    Additive.toMul
      (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
        K N j
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldEmbeddedFiniteAbstractField K N j)
          (numberFieldEmbeddedFiniteGaloisSubextension K N j)
          ((numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
            K N j).symm
            (Additive.ofMul
              (QuotientGroup.mk'
                (_root_.ideleClassNorm K N).range c))))) = _
  rw [← hclass,
    (numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
      K N j).symm_apply_apply]

/-- The standard finite-Galois norm-residue map is the explicit construction
for the standard chosen embedding of the common top field. -/
theorem
    globalNormResidueAbelianizationMonoidHom_eq_ofEmbedding_standard
    [FiniteDimensional K N] [IsGalois K N] :
    globalNormResidueAbelianizationMonoidHom K N =
      globalNormResidueAbelianizationMonoidHomOfEmbedding K N
        (numberFieldSeparableClosureEmbedding N) := by
  rfl

/-- In one common top-field embedding, the abstract relative norm between
the two base fixing subgroups is the ordinary idèle-class norm.  No
normality of the intermediate extension `M / K` is used. -/
theorem
    numberFieldEmbeddedIdeleClassEquivAmbientFixed_relativeNorm_of_commonTop
    [FiniteDimensional K N] [IsGalois K N]
    (j : N →ₐ[ℚ] SeparableClosure ℚ)
    (c : IdeleClassGroup M) :
    letI _ : FiniteDimensional K M :=
      commonTopBaseIntermediateFiniteDimensional K M N
    let H := numberFieldEmbeddedBaseSubgroup K N j
    let H' := numberFieldEmbeddedBaseSubgroup M N j
    let hH'H := numberFieldEmbeddedBaseSubgroup_le_of_commonTop K M N j
    letI _ : Finite (rationalFixedFieldAbsoluteQuotient H) :=
      (numberFieldEmbeddedFiniteAbstractField K N j).finite
    letI _ : Finite
        (rationalFixedFieldRelativeQuotient H H' hH'H) :=
      numberFieldEmbeddedBaseChangeExtensionQuotient_finite_of_commonTop
        K M N j
    relativeNorm rationalIdeleClassRepresentation H H' hH'H
        (numberFieldEmbeddedIdeleClassEquivAmbientFixed
          M N j (Additive.ofMul c)) =
      numberFieldEmbeddedIdeleClassEquivAmbientFixed
        K N j
        (Additive.ofMul (_root_.ideleClassNorm K M c)) := by
  dsimp only
  letI : FiniteDimensional K M :=
    commonTopBaseIntermediateFiniteDimensional K M N
  let H := numberFieldEmbeddedBaseSubgroup K N j
  let H' := numberFieldEmbeddedBaseSubgroup M N j
  let hH'H := numberFieldEmbeddedBaseSubgroup_le_of_commonTop K M N j
  letI hHfinite : Finite (rationalFixedFieldAbsoluteQuotient H) := by
    exact (numberFieldEmbeddedFiniteAbstractField K N j).finite
  letI hHH'finite : Finite
      (rationalFixedFieldRelativeQuotient H H' hH'H) :=
    numberFieldEmbeddedBaseChangeExtensionQuotient_finite_of_commonTop
      K M N j
  let F := abstractFixedField ℚ (SeparableClosure ℚ) H
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hH'H
  letI : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H hHfinite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H H' hH'H hHfinite hHH'finite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ F E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : NumberField E := NumberField.of_module_finite ℚ E
  letI : FiniteDimensional ℚ (E.restrictScalars ℚ) := by
    change FiniteDimensional ℚ E
    infer_instance
  let hE :
      E.restrictScalars ℚ =
        abstractFixedField ℚ (SeparableClosure ℚ) H' :=
    IntermediateField.extendScalars_restrictScalars
      (abstractFixedField_le ℚ (SeparableClosure ℚ) hH'H)
  letI hUpperFixedFiniteDimensional :
      FiniteDimensional ℚ
        (abstractFixedField ℚ (SeparableClosure ℚ) H') := by
    rw [← hE]
    infer_instance
  letI hUpperFixedNumberField :
      NumberField
        (abstractFixedField ℚ (SeparableClosure ℚ) H') :=
    NumberField.of_module_finite ℚ _
  let eRel :
      E ≃ₐ[ℚ] abstractFixedField ℚ (SeparableClosure ℚ) H' :=
    IntermediateField.equivOfEq hE
  let eK : K ≃ₐ[ℚ] F :=
    numberFieldEmbeddedAbstractBaseFieldEquiv K N j
  let eMBase :
      M ≃ₐ[ℚ] abstractFixedField ℚ (SeparableClosure ℚ) H' :=
    numberFieldEmbeddedAbstractBaseFieldEquiv M N j
  let eM : M ≃ₐ[ℚ] E := eMBase.trans eRel.symm
  have heM : eM.trans eRel = eMBase := by
    ext x
    simp only [eM, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
  have heRel :
      eRel.trans (IntermediateField.equivOfEq hE.symm) =
        (AlgEquiv.refl : E ≃ₐ[ℚ] E) := by
    cases hE
    rfl
  have hcompat (x : K) :
      eM (algebraMap K M x) = algebraMap F E (eK x) := by
    apply eRel.injective
    apply Subtype.ext
    change
      j (algebraMap M N (algebraMap K M x)) =
        j (algebraMap K N x)
    rw [IsScalarTower.algebraMap_apply K M N]
  have hupper :
      rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
          H H' hH'H
          (Additive.ofMul (ideleClassCongr eM c)) =
        numberFieldEmbeddedIdeleClassEquivAmbientFixed
          M N j (Additive.ofMul c) := by
    simp only [numberFieldEmbeddedIdeleClassEquivAmbientFixed,
      AddEquiv.trans_apply]
    apply Subtype.ext
    have hcongr := ideleClassCongr_trans eM eRel c
    have hcongrBase :
        ideleClassCongr (eM.trans eRel) c =
          ideleClassCongr eMBase c :=
      congrArg (fun e => ideleClassCongr e c) heM
    change
      ((rationalIdeleClassEquivFixed (E.restrictScalars ℚ))
          (Additive.ofMul (ideleClassCongr eM c))).1 =
        ((rationalIdeleClassEquivFixed
            (abstractFixedField ℚ (SeparableClosure ℚ) H'))
          (Additive.ofMul (ideleClassCongr eMBase c))).1
    calc
      _ =
          ((rationalIdeleClassEquivFixed
              (abstractFixedField ℚ (SeparableClosure ℚ) H'))
            (MulEquiv.toAdditive (ideleClassCongr eRel)
              (Additive.ofMul (ideleClassCongr eM c)))).1 := by
        exact
          (rationalIdeleClassEquivFixed_congr_apply_val
            hE.symm eRel heRel
            (Additive.ofMul (ideleClassCongr eM c))).symm
      _ = _ := by
        apply congrArg
          (fun d =>
            ((rationalIdeleClassEquivFixed
              (abstractFixedField ℚ (SeparableClosure ℚ) H')) d).1)
        exact congrArg Additive.ofMul (hcongr.trans hcongrBase)
  rw [← hupper]
  have hrelative :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_relativeNorm_ofFiniteTower
      H H' hH'H
  unfold rationalAbstractRelativeFixedFieldNormStatement at hrelative
  have hrelativec := hrelative (ideleClassCongr eM c)
  change
    relativeNorm rationalIdeleClassRepresentation H H' hH'H
        (rationalAbstractRelativeFixedFieldIdeleClassEquivFixed
          H H' hH'H
          (Additive.ofMul (ideleClassCongr eM c))) =
      rationalAbstractFixedFieldIdeleClassEquivFixed H
        (Additive.ofMul
          (_root_.ideleClassNorm F E (ideleClassCongr eM c)))
    at hrelativec
  rw [hrelativec]
  simp only [numberFieldEmbeddedIdeleClassEquivAmbientFixed,
    AddEquiv.trans_apply]
  change
    rationalAbstractFixedFieldIdeleClassEquivFixed H
        (Additive.ofMul
          (_root_.ideleClassNorm F E (ideleClassCongr eM c))) =
      rationalAbstractFixedFieldIdeleClassEquivFixed H
        (Additive.ofMul
          (ideleClassCongr eK (_root_.ideleClassNorm K M c)))
  apply congrArg (rationalAbstractFixedFieldIdeleClassEquivFixed H)
  apply congrArg Additive.ofMul
  exact (ideleClassCongr_ideleClassNorm eK eM hcompat c).symm

/-- The canonical quotient-to-Galois comparisons for one common top-field
embedding intertwine abstract restriction with restriction on actual Galois
groups, after abelianization. -/
theorem
    numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization_restriction
    [FiniteDimensional K N] [IsGalois K N]
    (j : N →ₐ[ℚ] SeparableClosure ℚ) :
    letI _ : FiniteDimensional K M :=
      commonTopBaseIntermediateFiniteDimensional K M N
    letI _ : FiniteDimensional M N :=
      commonTopIntermediateTopFiniteDimensional K M N
    letI _ : IsGalois M N :=
      commonTopIntermediateTopIsGalois K M N
    ∀ z : Abelianization
        (numberFieldEmbeddedFiniteGaloisSubextension M N j).extensionQuotient,
    let H := numberFieldEmbeddedBaseSubgroup K N j
    let H' := numberFieldEmbeddedBaseSubgroup M N j
    let J := numberFieldEmbeddedTopSubgroup K N j
    let hJH := numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j
    let hJH' : J.toSubgroup ≤ H'.toSubgroup :=
      numberFieldEmbeddedTopSubgroup_le_baseSubgroup M N j
    let hH'H := numberFieldEmbeddedBaseSubgroup_le_of_commonTop K M N j
    letI _ : (extensionSubgroup H J hJH).Normal :=
      numberFieldEmbeddedExtensionSubgroup_normal K N j
    letI _ : (extensionSubgroup H' J hJH').Normal :=
      numberFieldEmbeddedExtensionSubgroup_normal M N j
    Abelianization.map
        (AlgEquiv.restrictScalarsHom K : Gal(N / M) →* Gal(N / K))
        (Additive.toMul
          (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
            M N j (Additive.ofMul z))) =
      Additive.toMul
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
          K N j
          (MonoidHom.toAdditive
            (normResidueNaturalityAbelianizedRestriction
              H H' J J hJH hJH' hH'H le_rfl)
            (Additive.ofMul z))) := by
  dsimp only
  letI : FiniteDimensional K M :=
    commonTopBaseIntermediateFiniteDimensional K M N
  letI : FiniteDimensional M N :=
    commonTopIntermediateTopFiniteDimensional K M N
  letI : IsGalois M N :=
    commonTopIntermediateTopIsGalois K M N
  intro z
  let H := numberFieldEmbeddedBaseSubgroup K N j
  let H' := numberFieldEmbeddedBaseSubgroup M N j
  let J := numberFieldEmbeddedTopSubgroup K N j
  let hJH := numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j
  let hJH' : J.toSubgroup ≤ H'.toSubgroup :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup M N j
  let hH'H := numberFieldEmbeddedBaseSubgroup_le_of_commonTop K M N j
  letI hLowerNormal : (extensionSubgroup H J hJH).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal K N j
  letI hUpperNormal : (extensionSubgroup H' J hJH').Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal M N j
  let qLowerRaw :
      (H.toSubgroup ⧸ extensionSubgroup H J hJH) ≃* Gal(N / K) :=
    numberFieldEmbeddedExtensionQuotientEquivGaloisGroup K N j
  let qUpperRaw :
      (H'.toSubgroup ⧸ extensionSubgroup H' J hJH') ≃* Gal(N / M) :=
    numberFieldEmbeddedExtensionQuotientEquivGaloisGroup M N j
  let restrictActual : Gal(N / M) →* Gal(N / K) :=
    AlgEquiv.restrictScalarsHom K
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨sigma, rfl⟩ :=
    (numberFieldEmbeddedFiniteGaloisSubextension M N j).extensionQuotientMk_surjective q
  change
    Abelianization.map restrictActual
        (qUpperRaw.abelianizationCongr
          (Abelianization.of (QuotientGroup.mk sigma))) =
      qLowerRaw.abelianizationCongr
        (normResidueNaturalityAbelianizedRestriction
          H H' J J hJH hJH' hH'H le_rfl
          (Abelianization.of (QuotientGroup.mk sigma)))
  rw [normResidueNaturalityAbelianizedRestriction_of_mk,
    abelianizationCongr_of, abelianizationCongr_of,
    Abelianization.map_of]
  have hraw :
      restrictActual (qUpperRaw (QuotientGroup.mk sigma)) =
        qLowerRaw
          (QuotientGroup.mk (Subgroup.inclusion hH'H sigma)) := by
    apply AlgEquiv.ext
    intro x
    apply j.injective
    letI hUpperAlgebra : Algebra M (SeparableClosure ℚ) :=
      numberFieldEmbeddedSeparableClosureAlgebra M N j
    let eUpper := numberFieldEmbeddedSeparableClosureEquiv M N j
    letI hLowerAlgebra : Algebra K (SeparableClosure ℚ) :=
      numberFieldEmbeddedSeparableClosureAlgebra K N j
    let eLower := numberFieldEmbeddedSeparableClosureEquiv K N j
    calc
      j (restrictActual (qUpperRaw (QuotientGroup.mk sigma)) x) =
          sigma.1.1 (j x) := by
        exact
          ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply
            ℚ M N j eUpper sigma x
      _ = (Subgroup.inclusion hH'H sigma).1.1 (j x) := rfl
      _ = j
          (qLowerRaw
            (QuotientGroup.mk (Subgroup.inclusion hH'H sigma)) x) := by
        exact
          (ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply
            ℚ K N j eLower (Subgroup.inclusion hH'H sigma) x).symm
  exact congrArg Abelianization.of hraw

/-- For one embedding of a common finite Galois overfield, the
abelianization-valued global norm-residue maps commute with ordinary
idèle-class norm and restriction.  The intermediate extension need not be
Galois. -/
theorem
    globalNormResidueAbelianizationMonoidHomOfEmbedding_norm_restriction
    [FiniteDimensional K N] [IsGalois K N]
    (j : N →ₐ[ℚ] SeparableClosure ℚ) :
    letI _ : FiniteDimensional K M :=
      commonTopBaseIntermediateFiniteDimensional K M N
    letI _ : FiniteDimensional M N :=
      commonTopIntermediateTopFiniteDimensional K M N
    letI _ : IsGalois M N :=
      commonTopIntermediateTopIsGalois K M N
    (Abelianization.map
        (AlgEquiv.restrictScalarsHom K : Gal(N / M) →* Gal(N / K))).comp
        (globalNormResidueAbelianizationMonoidHomOfEmbedding M N j) =
      (globalNormResidueAbelianizationMonoidHomOfEmbedding K N j).comp
        (_root_.ideleClassNorm K M) := by
  letI : FiniteDimensional K M :=
    commonTopBaseIntermediateFiniteDimensional K M N
  letI : FiniteDimensional M N :=
    commonTopIntermediateTopFiniteDimensional K M N
  letI : IsGalois M N :=
    commonTopIntermediateTopIsGalois K M N
  let H := numberFieldEmbeddedBaseSubgroup K N j
  let H' := numberFieldEmbeddedBaseSubgroup M N j
  let J := numberFieldEmbeddedTopSubgroup K N j
  let hJH := numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j
  let hJH' : J.toSubgroup ≤ H'.toSubgroup :=
    numberFieldEmbeddedTopSubgroup_le_baseSubgroup M N j
  let hH'H := numberFieldEmbeddedBaseSubgroup_le_of_commonTop K M N j
  letI hLowerNormal : (extensionSubgroup H J hJH).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal K N j
  letI hLowerFinite :
      Finite (H.toSubgroup ⧸ extensionSubgroup H J hJH) :=
    numberFieldEmbeddedExtensionQuotient_finite K N j
  letI hUpperNormal : (extensionSubgroup H' J hJH').Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal M N j
  letI hUpperFinite :
      Finite (H'.toSubgroup ⧸ extensionSubgroup H' J hJH') :=
    numberFieldEmbeddedExtensionQuotient_finite M N j
  let hHH'finite :=
    numberFieldEmbeddedBaseChangeExtensionQuotient_finite_of_commonTop
      K M N j
  let T :
      FiniteAbstractFieldExtension
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
    { field := numberFieldEmbeddedFiniteAbstractField M N j
      base := numberFieldEmbeddedFiniteAbstractField K N j
      below := hH'H
      finiteQuotient := hHH'finite }
  letI hTBaseNormal :
      (extensionSubgroup T.base.field J hJH).Normal := by
    change (extensionSubgroup H J hJH).Normal
    exact hLowerNormal
  letI hTBaseFinite :
      Finite
        (T.base.field.toSubgroup ⧸
          extensionSubgroup T.base.field J hJH) := by
    change Finite (H.toSubgroup ⧸ extensionSubgroup H J hJH)
    exact hLowerFinite
  letI hTFieldNormal :
      (extensionSubgroup T.field.field J hJH').Normal := by
    change (extensionSubgroup H' J hJH').Normal
    exact hUpperNormal
  letI hTFieldFinite :
      Finite
        (T.field.field.toSubgroup ⧸
          extensionSubgroup T.field.field J hJH') := by
    change Finite (H'.toSubgroup ⧸ extensionSubgroup H' J hJH')
    exact hUpperFinite
  let restrictActual : Gal(N / M) →* Gal(N / K) :=
    AlgEquiv.restrictScalarsHom K
  apply MonoidHom.ext
  intro c
  let a :=
    numberFieldEmbeddedIdeleClassEquivAmbientFixed
      M N j (Additive.ofMul c)
  have hnat :=
    DegreeData.normResidueNaturality_norm_restriction
      (D := rationalCyclotomicDegreeData)
      (A := rationalIdeleClassRepresentation)
      (v := rationalCyclotomicIdeleClassValuationData)
      (hcf := rationalIdeleClassRepresentation_satisfiesClassFieldAxiom)
      (T := T) (L := J) (L' := J)
      (hLnormal := hTBaseNormal)
      (hL'normal := hTFieldNormal)
      (hLKfinite := hTBaseFinite)
      (hL'K'finite := hTFieldFinite)
      hJH hJH' le_rfl
  have hnatc :=
    DFunLike.congr_fun hnat
      (finiteNormClass rationalIdeleClassRepresentation
        H' J hJH' a)
  change _ =
    rationalCyclotomicDegreeData.normResidueSymbol
      rationalIdeleClassRepresentation
      rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
      T.base
      { field := J
        below := hJH
        normal := hTBaseNormal
        finite := hTBaseFinite }
      (finiteReciprocityNaturalityNormMap
        rationalIdeleClassRepresentation
        T.base.field T.field.field J J
        hJH hJH' T.below le_rfl
        (finiteNormClass rationalIdeleClassRepresentation
          T.field.field J hJH' a)) at hnatc
  rw [finiteReciprocityNaturalityNormMap_finiteNormClass] at hnatc
  have hnorm :
      relativeNorm rationalIdeleClassRepresentation H H' hH'H a =
        numberFieldEmbeddedIdeleClassEquivAmbientFixed K N j
          (Additive.ofMul (_root_.ideleClassNorm K M c)) :=
    numberFieldEmbeddedIdeleClassEquivAmbientFixed_relativeNorm_of_commonTop
      K M N j c
  calc
    Abelianization.map restrictActual
        (globalNormResidueAbelianizationMonoidHomOfEmbedding M N j c) =
      Abelianization.map restrictActual
        (Additive.toMul
          (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
            M N j
            (rationalCyclotomicDegreeData.normResidueSymbol
              rationalIdeleClassRepresentation
              rationalCyclotomicIdeleClassValuationData
              rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
              (numberFieldEmbeddedFiniteAbstractField M N j)
              (numberFieldEmbeddedFiniteGaloisSubextension M N j)
              (finiteNormClass rationalIdeleClassRepresentation
                H' J hJH' a)))) := by
      rw [globalNormResidueAbelianizationMonoidHomOfEmbedding_apply]
    _ =
      Additive.toMul
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
          K N j
          (MonoidHom.toAdditive
            (normResidueNaturalityAbelianizedRestriction
              H H' J J hJH hJH' hH'H le_rfl)
            (rationalCyclotomicDegreeData.normResidueSymbol
              rationalIdeleClassRepresentation
              rationalCyclotomicIdeleClassValuationData
              rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
              (numberFieldEmbeddedFiniteAbstractField M N j)
              (numberFieldEmbeddedFiniteGaloisSubextension M N j)
              (finiteNormClass rationalIdeleClassRepresentation
                H' J hJH' a)))) := by
      exact
        numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization_restriction
          K M N j _
    _ =
      Additive.toMul
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
          K N j
          (rationalCyclotomicDegreeData.normResidueSymbol
            rationalIdeleClassRepresentation
            rationalCyclotomicIdeleClassValuationData
            rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
            (numberFieldEmbeddedFiniteAbstractField K N j)
            (numberFieldEmbeddedFiniteGaloisSubextension K N j)
            (finiteNormClass rationalIdeleClassRepresentation
              H J hJH
              (relativeNorm rationalIdeleClassRepresentation
                H H' hH'H a)))) := by
      exact congrArg
        (fun z =>
          Additive.toMul
            (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
              K N j z))
        hnatc
    _ =
      globalNormResidueAbelianizationMonoidHomOfEmbedding K N j
        (_root_.ideleClassNorm K M c) := by
      rw [hnorm,
        ← globalNormResidueAbelianizationMonoidHomOfEmbedding_apply]

/-- Global norm-residue naturality in Galois abelianizations for a finite
tower with a common Galois top field.  No Galois hypothesis is imposed on
the intermediate extension. -/
theorem globalNormResidueAbelianizationMonoidHom_norm_restriction
    [FiniteDimensional K N] [IsGalois K N] :
    letI _ : FiniteDimensional K M :=
      commonTopBaseIntermediateFiniteDimensional K M N
    letI _ : FiniteDimensional M N :=
      commonTopIntermediateTopFiniteDimensional K M N
    letI _ : IsGalois M N :=
      commonTopIntermediateTopIsGalois K M N
    (Abelianization.map
        (AlgEquiv.restrictScalarsHom K : Gal(N / M) →* Gal(N / K))).comp
        (globalNormResidueAbelianizationMonoidHom M N) =
      (globalNormResidueAbelianizationMonoidHom K N).comp
        (_root_.ideleClassNorm K M) := by
  letI : FiniteDimensional K M :=
    commonTopBaseIntermediateFiniteDimensional K M N
  letI : FiniteDimensional M N :=
    commonTopIntermediateTopFiniteDimensional K M N
  letI : IsGalois M N :=
    commonTopIntermediateTopIsGalois K M N
  rw [globalNormResidueAbelianizationMonoidHom_eq_ofEmbedding_standard,
    globalNormResidueAbelianizationMonoidHom_eq_ofEmbedding_standard]
  exact
    globalNormResidueAbelianizationMonoidHomOfEmbedding_norm_restriction
      K M N (numberFieldSeparableClosureEmbedding N)

end CommonTop

end Reciprocity
end GlobalClassFieldTheory

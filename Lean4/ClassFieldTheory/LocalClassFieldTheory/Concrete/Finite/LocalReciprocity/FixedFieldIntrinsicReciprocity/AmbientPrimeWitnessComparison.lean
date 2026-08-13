import Mathlib.FieldTheory.Galois.Basic
import LocalClassFieldTheory.Concrete.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeSymbolSetup
import LocalClassFieldTheory.Concrete.Finite.LocalReciprocity.ConcreteReciprocityPrimeNorm
import LocalClassFieldTheory.Concrete.Finite.LocalReciprocity.Main

/-!
# Local and ambient comparison for prime witnesses

The chosen ambient prime witness represents the prescribed abelianized
Galois element both under the concrete local Artin map and under the
ambient fixed-field norm-residue construction.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- The chosen ambient prime witness maps to the prescribed abelianized
Galois element under the concrete local Artin map. -/
theorem
    ambientEmbeddedPrimeWitness_local
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    (j : E →ₐ[K] SeparableClosure K)
    (e : ambientEmbeddedSeparableClosureEquiv K F E j)
    (z : Abelianization Gal(E / F)) :
    localArtinMonoidHom F E
        (ambientEmbeddedPrimeWitness K F E j e z) =
      z := by
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  letI : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun x => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  let EI :=
    finiteGaloisAbstractExtensionOfEmbedding F E jI
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    apply (AlgHom.fieldRange i).fixingSubgroup_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  letI hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  letI hSourceFinite : Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below) :=
    EI.finite
  letI hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  letI hTargetFinite : Finite
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
    ambientEmbeddedExtensionQuotient_finite K F E j e
  letI hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨H₀, ambientEmbeddedAbsoluteQuotientFinite K F i⟩
  let qF :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
      F E jI
  let RF :=
    (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
      (localResidueDatum F)
  letI _hRFFinite : Finite
      (RF.field.toSubgroup ⧸
        extensionSubgroup RF.field EI.field EI.below) := by
    change Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below)
    exact hSourceFinite
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  let zF : Abelianization EI.extensionQuotient :=
    qF.abelianizationCongr.symm z
  let q :=
    Classical.choose (QuotientGroup.mk_surjective zF)
  have hq :=
    Classical.choose_spec (QuotientGroup.mk_surjective zF)
  let sigma :=
    Classical.choose
      ((localResidueDatum F).frobeniusRestriction_surjective
        RF EI.field EI.below q)
  have hsigma :=
    Classical.choose_spec
      ((localResidueDatum F).frobeniusRestriction_surjective
        RF EI.field EI.below q)
  let sigmaH :=
    intrinsicFrobeniusElementToAmbientEmbeddedField
      K F E j e sigma
  let SF :=
    (localResidueDatum F).frobeniusFixedField
      RF EI.field EI.below sigma
  let hSFB :=
    (localResidueDatum F).frobeniusFixedField_le
      RF EI.field EI.below sigma
  let hSFabsolute :=
    (localResidueDatum F).frobeniusFixedField_absoluteFinite
      (intrinsicFiniteAbstractBase F) EI.field EI.below sigma
  let hSFfinite :=
    (localResidueDatum F).frobeniusFixedField_finite
      RF EI.field EI.below sigma
  letI _hSFFinite : Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) SF hSFB) := by
    change Finite
      (RF.field.toSubgroup ⧸
        extensionSubgroup RF.field SF hSFB)
    exact hSFfinite
  let SigmaF : FiniteAbstractField
      Gal(SeparableClosure F / F) :=
    ⟨SF, hSFabsolute⟩
  let LF :=
    abstractFixedField F (SeparableClosure F) SF
  let SH :=
    (localResidueDatum K).frobeniusFixedField
      RH J₀ hJH sigmaH
  let hSHH :=
    (localResidueDatum K).frobeniusFixedField_le
      RH J₀ hJH sigmaH
  let hSHabsolute :=
    (localResidueDatum K).frobeniusFixedField_absoluteFinite
      H J₀ hJH sigmaH
  let LH :=
    abstractRelativeFixedField K (SeparableClosure K) hSHH
  let iLH : F →ₐ[K] LH :=
    i.codRestrict (LH.restrictScalars K).toSubalgebra (fun x => by
      change i x ∈ IntermediateField.fixedField SH.toSubgroup
      rw [IntermediateField.mem_fixedField_iff]
      intro rho hrho
      have hrhoH : rho ∈ H₀.toSubgroup :=
        hSHH hrho
      change rho (i x) = i x
      change
        rho ∈ (AlgHom.fieldRange i).fixingSubgroup at hrhoH
      rw [IntermediateField.mem_fixingSubgroup_iff] at hrhoH
      exact hrhoH (i x) ⟨x, rfl⟩)
  letI : Algebra F LH :=
    iLH.toRingHom.toAlgebra
  let phi :=
    intrinsicFrobeniusFixedFieldEquivAmbientEmbeddedField
      K F E j e sigma
  letI : FiniteDimensional F
      (abstractFixedField F (SeparableClosure F) SF) :=
    abstractFixedField_finiteDimensional
      F (SeparableClosure F) SF hSFabsolute
  letI : NontriviallyNormedField
      (abstractFixedField F (SeparableClosure F) SF) :=
    finiteExtensionSpectralNormedField
      F (abstractFixedField F (SeparableClosure F) SF)
  letI : ValuativeRel
      (abstractFixedField F (SeparableClosure F) SF) :=
    finiteExtensionSpectralValuativeRel
      F (abstractFixedField F (SeparableClosure F) SF)
  letI : IsNonarchimedeanLocalField
      (abstractFixedField F (SeparableClosure F) SF) :=
    finiteExtensionSpectralIsNonarchimedeanLocalField
      F (abstractFixedField F (SeparableClosure F) SF)
  letI : Valuation.HasExtension
      (ValuativeRel.valuation F)
      (ValuativeRel.valuation
        (abstractFixedField F (SeparableClosure F) SF)) :=
    finiteExtensionSpectralValuation_hasExtension
      F (abstractFixedField F (SeparableClosure F) SF)
  letI : FiniteDimensional K LH :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) SH hSHabsolute
  let iH : LH →ₐ[K] SeparableClosure K :=
    LH.val.restrictScalars K
  letI : IsScalarTower K LH (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      exact (iH.commutes x).symm)
  letI : Algebra.IsSeparable K LH :=
    Algebra.isSeparable_tower_bot_of_isSeparable
      K LH (SeparableClosure K)
  letI : NontriviallyNormedField LH :=
    finiteExtensionSpectralNormedField K LH
  letI : ValuativeRel LH :=
    finiteExtensionSpectralValuativeRel K LH
  letI : IsNonarchimedeanLocalField LH :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K LH
  letI : Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation LH) :=
    finiteExtensionSpectralValuation_hasExtension K LH
  have hsourceRing :
      (localSeparableValuationSubring F).comap LF.val.toRingHom =
        (ValuativeRel.valuation LF).valuationSubring :=
    localSeparableValuationSubring_comap_embedding F LF LF.val
  have htargetRing :
      (localSeparableValuationSubring K).comap iH.toRingHom =
        (ValuativeRel.valuation LH).valuationSubring :=
    localSeparableValuationSubring_comap_embedding K LH iH
  have hmem (x : LF) :
      x ∈ (ValuativeRel.valuation LF).valuationSubring ↔
        phi x ∈ (ValuativeRel.valuation LH).valuationSubring := by
    rw [← hsourceRing, ← htargetRing]
    change
      (x : SeparableClosure F) ∈ localSeparableValuationSubring F ↔
        ((phi x : LH) : SeparableClosure K) ∈
          localSeparableValuationSubring K
    have hphiVal :
        ((phi x : LH) : SeparableClosure K) =
          e (x : SeparableClosure F) := by
      exact
        intrinsicFrobeniusFixedFieldEquivAmbientEmbeddedField_apply_val
          K F E j e sigma x
    rw [hphiVal]
    have hvaluation :=
      localSeparableValuationSubring_eq_comap_finiteExtensionEquiv
        K F i e
    rw [hvaluation]
    rfl
  let pF :=
    chosenValuationOneUnitOfRingEquiv LF LH phi hmem
  have hpFvalue :=
    chosenValuationOneUnitOfRingEquiv_source LF LH phi hmem
  let piF : ambientFixedAddSubgroup
      (intrinsicAbsoluteUnits F) SF :=
    abstractFixedFieldUnitsEquivGaloisFixed
      F (SeparableClosure F) SF
        (Additive.ofMul pF)
  have hpiF :
      (localHenselianValuation F).IsPrimeElement SigmaF piF := by
    exact
      localHenselianValuation_isPrimeElement_abstractFixedField
        F SigmaF pF hpFvalue
  let xPrime : Fˣ :=
    normUnits F LF pF
  have hnormF :
      relativeNorm (intrinsicAbsoluteUnits F)
          (intrinsicAbstractBase F) SF hSFB piF =
        baseUnitsEquivGaloisAmbientFixed F (SeparableClosure F)
          (Additive.ofMul xPrime) := by
    exact
      relativeNorm_intrinsicAbstractBase_abstractFixedFieldUnit
        F SF hSFB pF
  have hconcretePrime :
      concreteNormResidueSymbolOfEmbedding
          F E jI
          (localResidueDatum F)
          (localHenselianValuation F)
          (separableClosureUnits_isClassFormation F) xPrime =
        Abelianization.of (qF q) := by
    have hprime :=
      concreteNormResidueSymbolOfEmbedding_apply_primeNorm
        F E jI
        (localResidueDatum F)
        (localHenselianValuation F)
        (separableClosureUnits_isClassFormation F)
        q sigma hsigma piF hpiF xPrime
        (by
          simpa only [RF, SF, hSFB] using hnormF.symm)
    exact hprime
  have hqz :
      qF.abelianizationCongr (Abelianization.of q) = z := by
    calc
      qF.abelianizationCongr (Abelianization.of q) =
          qF.abelianizationCongr zF :=
        congrArg qF.abelianizationCongr hq
      _ = z :=
        qF.abelianizationCongr.apply_symm_apply z
  have hconcretePrimeZ :
      concreteNormResidueSymbolOfEmbedding
          F E jI
          (localResidueDatum F)
          (localHenselianValuation F)
          (separableClosureUnits_isClassFormation F) xPrime = z := by
    rw [hconcretePrime, ← hqz]
    exact (abelianizationCongr_of qF q).symm
  have hxWitness :
      ambientEmbeddedPrimeWitness K F E j e z = xPrime := by
    exact
      ambientEmbeddedPrimeWitness_formula K F E j e z
  rw [hxWitness]
  exact
    (DFunLike.congr_fun
      (localArtinMonoidHom_eq_of_embedding F E jI) xPrime).trans
      hconcretePrimeZ

/-- The chosen prime witness satisfies the ambient fixed-field
norm-residue symbol formula. -/
theorem
    ambientEmbeddedPrimeWitness_symbol
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    (j : E →ₐ[K] SeparableClosure K)
    (e : ambientEmbeddedSeparableClosureEquiv K F E j)
    (z : Abelianization Gal(E / F)) :
    ambientEmbeddedPrimeSymbolProperty K F E j e z := by
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  letI : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun x => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  let EI :=
    finiteGaloisAbstractExtensionOfEmbedding F E jI
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    apply (AlgHom.fieldRange i).fixingSubgroup_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  letI hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  letI hSourceFinite : Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below) :=
    EI.finite
  letI hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  letI hTargetFinite : Finite
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
    ambientEmbeddedExtensionQuotient_finite K F E j e
  letI hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨H₀, ambientEmbeddedAbsoluteQuotientFinite K F i⟩
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H₀
  have hfixed :
      F₀ = AlgHom.fieldRange i :=
    InfiniteGalois.fixedField_fixingSubgroup
      (AlgHom.fieldRange i)
  let phiF : F ≃ₐ[K] F₀ :=
    (i.equivFieldRange).trans
      (IntermediateField.equivOfEq hfixed.symm)
  let qF :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
      F E jI
  let q₀ :=
    abstractExtensionQuotientEquivGaloisGroup
      K (SeparableClosure K) H₀ J₀ hJH hTargetNormal
  let RF :=
    (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
      (localResidueDatum F)
  letI _hRFFinite : Finite
      (RF.field.toSubgroup ⧸
        extensionSubgroup RF.field EI.field EI.below) := by
    change Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below)
    exact hSourceFinite
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  let zF : Abelianization EI.extensionQuotient :=
    qF.abelianizationCongr.symm z
  let q :=
    Classical.choose (QuotientGroup.mk_surjective zF)
  let sigma :=
    Classical.choose
      ((localResidueDatum F).frobeniusRestriction_surjective
        RF EI.field EI.below q)
  let sigmaH :=
    intrinsicFrobeniusElementToAmbientEmbeddedField
      K F E j e sigma
  let qAmbient :=
    (localResidueDatum K).frobeniusRestriction
      RH J₀ hJH sigmaH
  let SF :=
    (localResidueDatum F).frobeniusFixedField
      RF EI.field EI.below sigma
  let hSFabsolute :=
    (localResidueDatum F).frobeniusFixedField_absoluteFinite
      (intrinsicFiniteAbstractBase F) EI.field EI.below sigma
  let LF :=
    abstractFixedField F (SeparableClosure F) SF
  let SH :=
    (localResidueDatum K).frobeniusFixedField
      RH J₀ hJH sigmaH
  let hSHH :=
    (localResidueDatum K).frobeniusFixedField_le
      RH J₀ hJH sigmaH
  let hSHfinite :=
    (localResidueDatum K).frobeniusFixedField_finite
      RH J₀ hJH sigmaH
  letI _hSHFinite : Finite
      (H₀.toSubgroup ⧸
        extensionSubgroup H₀ SH hSHH) := by
    change Finite
      (RH.field.toSubgroup ⧸
        extensionSubgroup RH.field SH hSHH)
    exact hSHfinite
  let hSHabsolute :=
    (localResidueDatum K).frobeniusFixedField_absoluteFinite
      H J₀ hJH sigmaH
  let LH :=
    abstractRelativeFixedField K (SeparableClosure K) hSHH
  let iLH : F →ₐ[K] LH :=
    i.codRestrict (LH.restrictScalars K).toSubalgebra (fun x => by
      change i x ∈ IntermediateField.fixedField SH.toSubgroup
      rw [IntermediateField.mem_fixedField_iff]
      intro rho hrho
      have hrhoH : rho ∈ H₀.toSubgroup :=
        hSHH hrho
      change rho (i x) = i x
      change
        rho ∈ (AlgHom.fieldRange i).fixingSubgroup at hrhoH
      rw [IntermediateField.mem_fixingSubgroup_iff] at hrhoH
      exact hrhoH (i x) ⟨x, rfl⟩)
  letI : Algebra F LH :=
    iLH.toRingHom.toAlgebra
  let phi :=
    intrinsicFrobeniusFixedFieldEquivAmbientEmbeddedField
      K F E j e sigma
  have hphiComm :
      RingHom.comp (algebraMap F₀ LH) phiF.toRingEquiv.toRingHom =
        RingHom.comp phi.toRingEquiv.toRingHom
          (algebraMap F LF) := by
    apply RingHom.ext
    intro x
    change
      algebraMap F₀ LH (phiF x) =
        phi (algebraMap F LF x)
    calc
      algebraMap F₀ LH (phiF x) =
          algebraMap F LH x := by
        apply LH.val.injective
        rfl
      _ = phi (algebraMap F LF x) :=
        (phi.commutes x).symm
  letI : FiniteDimensional F LF :=
    abstractFixedField_finiteDimensional
      F (SeparableClosure F) SF hSFabsolute
  letI : NontriviallyNormedField LF :=
    finiteExtensionSpectralNormedField F LF
  letI : ValuativeRel LF :=
    finiteExtensionSpectralValuativeRel F LF
  letI : IsNonarchimedeanLocalField LF :=
    finiteExtensionSpectralIsNonarchimedeanLocalField F LF
  letI : Valuation.HasExtension
      (ValuativeRel.valuation F) (ValuativeRel.valuation LF) :=
    finiteExtensionSpectralValuation_hasExtension F LF
  letI : FiniteDimensional K LH :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) SH hSHabsolute
  letI : FiniteDimensional K F₀ :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H₀ hHabsolute
  letI hF₀LHFinite : FiniteDimensional F₀ LH :=
    abstractRelativeFixedField_finiteDimensional
      K (SeparableClosure K) H₀ SH hSHH hHabsolute _hSHFinite
  let iH : LH →ₐ[K] SeparableClosure K :=
    LH.val.restrictScalars K
  letI : IsScalarTower K LH (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      exact (iH.commutes x).symm)
  letI : Algebra.IsSeparable K LH :=
    Algebra.isSeparable_tower_bot_of_isSeparable
      K LH (SeparableClosure K)
  letI hLHNorm : NontriviallyNormedField LH :=
    finiteExtensionSpectralNormedField K LH
  letI hLHVal : ValuativeRel LH :=
    finiteExtensionSpectralValuativeRel K LH
  letI hLHLocal : IsNonarchimedeanLocalField LH :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K LH
  letI : Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation LH) :=
    finiteExtensionSpectralValuation_hasExtension K LH
  have hmem (x : LF) :
      x ∈ (ValuativeRel.valuation LF).valuationSubring ↔
        phi x ∈ (ValuativeRel.valuation LH).valuationSubring := by
    exact
      valuationSubring_mem_iff_of_separableClosureRingEquiv
        F K LF LH LF.val iH e.toRingEquiv
        (localSeparableValuationSubring_eq_comap_finiteExtensionEquiv
          K F i e)
        phi.toRingEquiv
        (fun y =>
          intrinsicFrobeniusFixedFieldEquivAmbientEmbeddedField_apply_val
            K F E j e sigma y)
        x
  let pF :=
    chosenValuationOneUnitOfRingEquiv LF LH phi hmem
  let xPrime : Fˣ :=
    normUnits F LF pF
  let xPrime0 : F₀ˣ :=
    Units.mapEquiv phiF.toMulEquiv xPrime
  have hxWitness :
      ambientEmbeddedPrimeWitness K F E j e z = xPrime := by
    rfl
  have hpHvalue :=
    chosenValuationOneUnitOfRingEquiv_target LF LH phi hmem
  let pH : LHˣ :=
    Units.mapEquiv phi.toMulEquiv pF
  change
    IsNonarchimedeanLocalField.valuationMap LH
      (Additive.ofMul pH) = 1 at hpHvalue
  let SigmaH : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨SH, hSHabsolute⟩
  let piH : ambientFixedAddSubgroup
      (galoisAmbientUnitsRep K (SeparableClosure K)) SH :=
    abstractRelativeFixedFieldUnitsEquivGaloisFixed
      K (SeparableClosure K) H₀ SH hSHH
        (Additive.ofMul pH)
  have hpiH :
      (localHenselianValuation K).IsPrimeElement SigmaH piH := by
    exact
      localHenselianValuation_isPrimeElement_abstractFixedField
        K SigmaH pH hpHvalue
  have hambientPrime :
      abstractFixedFieldNormResidueSymbol
          K (SeparableClosure K)
          (localResidueDatum K)
          (localHenselianValuation K)
          (separableClosureUnits_isClassFormation K)
          H₀ J₀ hJH (Additive.ofMul xPrime0) =
        Additive.ofMul
          (q₀.abelianizationCongr
            (Abelianization.of qAmbient)) := by
    exact
      abstractFixedFieldNormResidueSymbol_eq_of_transportedValuationOneUnit
        K F LF H J₀ hJH sigmaH
          (_hLHNorm := hLHNorm)
          (_hLHVal := hLHVal)
          (_hLHLocal := hLHLocal)
          (_hF₀LHFinite := hF₀LHFinite)
          phiF.toRingEquiv phi.toRingEquiv hphiComm hmem hpiH
  have hxPrime0 :
      Units.mapEquiv phiF.toMulEquiv
          (ambientEmbeddedPrimeWitness K F E j e z) =
        xPrime0 := by
    exact congrArg
      (Units.mapEquiv phiF.toMulEquiv) hxWitness
  have hsymbolWitness :
      abstractFixedFieldNormResidueSymbol
          K (SeparableClosure K)
          (localResidueDatum K)
          (localHenselianValuation K)
          (separableClosureUnits_isClassFormation K)
          H₀ J₀ hJH
          (Additive.ofMul
            (Units.mapEquiv phiF.toMulEquiv
              (ambientEmbeddedPrimeWitness K F E j e z))) =
        Additive.ofMul
          (q₀.abelianizationCongr
            (Abelianization.of qAmbient)) := by
    exact
      (congrArg
        (fun y : F₀ˣ =>
          abstractFixedFieldNormResidueSymbol
            K (SeparableClosure K)
            (localResidueDatum K)
            (localHenselianValuation K)
            (separableClosureUnits_isClassFormation K)
            H₀ J₀ hJH (Additive.ofMul y))
        hxPrime0).trans hambientPrime
  unfold ambientEmbeddedPrimeSymbolProperty
  exact hsymbolWitness

/-- The transported ambient symbol of the chosen prime witness equals
its ambient Frobenius target. -/
theorem
    ambientEmbeddedPrimeTransportValue_eq_target
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    (j : E →ₐ[K] SeparableClosure K)
    (e : ambientEmbeddedSeparableClosureEquiv K F E j)
    (z : Abelianization Gal(E / F)) :
    ambientEmbeddedPrimeTransportValue K F E j e z =
      ambientEmbeddedPrimeTarget K F E j e z := by
  have hsymbol :=
    ambientEmbeddedPrimeWitness_symbol K F E j e z
  unfold ambientEmbeddedPrimeSymbolProperty at hsymbol
  exact
    (ambientEmbeddedPrimeTransportValue_eq_target_of_symbol
      K F E j e z hsymbol)

/-- The ambient Frobenius target recovers the original abelianized
Galois element. -/
theorem
    ambientEmbeddedPrimeTarget_eq
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    (j : E →ₐ[K] SeparableClosure K)
    (e : ambientEmbeddedSeparableClosureEquiv K F E j)
    (z : Abelianization Gal(E / F)) :
    ambientEmbeddedPrimeTarget K F E j e z = z := by
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  letI : Algebra F (SeparableClosure F) :=
    (separableClosure F (AlgebraicClosure F)).algebra
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun x => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  let EI :=
    finiteGaloisAbstractExtensionOfEmbedding F E jI
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    apply (AlgHom.fieldRange i).fixingSubgroup_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  letI hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  letI hSourceFinite : Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below) :=
    EI.finite
  letI hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  letI hTargetFinite : Finite
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) :=
    ambientEmbeddedExtensionQuotient_finite K F E j e
  letI hHabsolute : Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H₀ (le_baseField H₀)) := by
    exact ambientEmbeddedAbsoluteQuotientFinite K F i
  let H : FiniteAbstractField
      Gal(SeparableClosure K / K) :=
    ⟨H₀, ambientEmbeddedAbsoluteQuotientFinite K F i⟩
  let qF :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
      F E jI
  let qE :=
    ambientEmbeddedExtensionQuotientEquivGaloisGroup
      K F E j e
  let RF :=
    (intrinsicFiniteAbstractBase F).toFiniteResidueAbstractField
      (localResidueDatum F)
  letI _hRFFinite : Finite
      (RF.field.toSubgroup ⧸
        extensionSubgroup RF.field EI.field EI.below) := by
    change Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below)
    exact hSourceFinite
  let RH :=
    H.toFiniteResidueAbstractField (localResidueDatum K)
  let zF : Abelianization EI.extensionQuotient :=
    qF.abelianizationCongr.symm z
  let q :=
    Classical.choose (QuotientGroup.mk_surjective zF)
  have hq :=
    Classical.choose_spec (QuotientGroup.mk_surjective zF)
  let sigma :=
    Classical.choose
      ((localResidueDatum F).frobeniusRestriction_surjective
        RF EI.field EI.below q)
  have hsigma :=
    Classical.choose_spec
      ((localResidueDatum F).frobeniusRestriction_surjective
        RF EI.field EI.below q)
  let sigmaH :=
    intrinsicFrobeniusElementToAmbientEmbeddedField
      K F E j e sigma
  let qAmbient :=
    (localResidueDatum K).frobeniusRestriction
      RH J₀ hJH sigmaH
  have hrestriction :
      qE qAmbient = qF q := by
    calc
      qE qAmbient =
          qF ((localResidueDatum F).frobeniusRestriction
            RF EI.field EI.below sigma) :=
        intrinsicFrobeniusRestriction_compatibility_ambientEmbeddedField
          K F E j e sigma
      _ = qF q := congrArg qF hsigma
  have hqz :
      qF.abelianizationCongr (Abelianization.of q) = z := by
    calc
      qF.abelianizationCongr (Abelianization.of q) =
          qF.abelianizationCongr zF :=
        congrArg qF.abelianizationCongr hq
      _ = z :=
        qF.abelianizationCongr.apply_symm_apply z
  have htarget :
      ambientEmbeddedPrimeTarget K F E j e z =
        qE.abelianizationCongr
          (Abelianization.of qAmbient) := by
    rfl
  rw [htarget]
  calc
    qE.abelianizationCongr
        (Abelianization.of qAmbient) =
        Abelianization.of (qE qAmbient) :=
      abelianizationCongr_of qE qAmbient
    _ = Abelianization.of (qF q) :=
      congrArg Abelianization.of hrestriction
    _ = qF.abelianizationCongr
          (Abelianization.of q) :=
      (abelianizationCongr_of qF q).symm
    _ = z := hqz

/-- The ambient norm-residue value of the chosen prime witness is the
prescribed abelianized Galois element. -/
theorem
    ambientEmbeddedPrimeWitness_ambient
    (K F E : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    (j : E →ₐ[K] SeparableClosure K)
    (e : ambientEmbeddedSeparableClosureEquiv K F E j)
    (z : Abelianization Gal(E / F)) :
    ambientEmbeddedNormResidueAbelianElement K F E j e
        (ambientEmbeddedPrimeWitness K F E j e z) =
      z := by
  calc
    ambientEmbeddedNormResidueAbelianElement K F E j e
        (ambientEmbeddedPrimeWitness K F E j e z) =
        ambientEmbeddedPrimeTransportValue K F E j e z := rfl
    _ = ambientEmbeddedPrimeTarget K F E j e z :=
      ambientEmbeddedPrimeTransportValue_eq_target K F E j e z
    _ = z :=
      ambientEmbeddedPrimeTarget_eq K F E j e z

end LocalClassFieldTheory

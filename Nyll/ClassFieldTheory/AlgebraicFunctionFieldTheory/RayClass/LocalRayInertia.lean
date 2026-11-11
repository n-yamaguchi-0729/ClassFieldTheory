/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayDecomposition
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RayArtinRamification
public import Nyll.AlgebraicCurves.Places.Ramification.PlaceFiberCenterEquivariance
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteRestriction
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GlobalDecomposition
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.DecompositionResidue
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.CompactUnits
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Topology
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Topology
public import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationInertiaCompact
public import Nyll.SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage

/-!
# Native normalization inertia and the original local unit image

The valuation ring of the place attached to a finite normalization prime
is its actual localization. Comparing the two original actions on the
coefficient ring proves that residue inertia is exactly normalization
inertia. This comparison uses the original residue map at the original
prime and does not replace the residue field or its Galois action.

The original finite restriction maps and compactness then identify the
absolute normalization-inertia image with the actual local ordinary-unit
Artin image, before taking the ray quotient.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicCurve IsDedekindDomain LocalClassFieldTheory
open EtaleFundamentalGroups.Inertia
open scoped Pointwise

namespace FunctionField

attribute [local instance] normalizationCommAlgGaloisAction

namespace IdeleGroup

section FiniteNormalization

attribute [local instance] AlgebraicCurve.Place.fiberNormalizationAction

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (v : Place k K)

local instance finitePrimeValuationAlgebra
    (P : HeightOneSpectrum (Place.integralClosureAt L v)) :
    Algebra (Place.integralClosureAt L v) (Place.placeOfPrime P).toValuationSubring := by
  change Algebra (Place.integralClosureAt L v)
    (HeightOneSpectrum.valuationSubringAtPrime L P)
  infer_instance

private local instance finitePrimeValuationTower
    (P : HeightOneSpectrum (Place.integralClosureAt L v)) :
    IsScalarTower (Place.integralClosureAt L v) (Place.placeOfPrime P).toValuationSubring L := by
  change IsScalarTower (Place.integralClosureAt L v)
    (HeightOneSpectrum.valuationSubringAtPrime L P) L
  infer_instance

private local instance finitePrimeValuationLocalization
    (P : HeightOneSpectrum (Place.integralClosureAt L v)) :
    IsLocalization.AtPrime (Place.placeOfPrime P).toValuationSubring P.asIdeal := by
  change IsLocalization.AtPrime (HeightOneSpectrum.valuationSubringAtPrime L P) P.asIdeal
  infer_instance

/-- The original decomposition action on the place valuation ring
extends the original normalization action through its actual inclusion. -/
theorem decompositionValuationEquiv_normalization_algebraMap
    (P : HeightOneSpectrum (Place.integralClosureAt L v))
    (σ : decompositionGroup (K := K) (Place.placeOfPrime P))
    (b : Place.integralClosureAt L v) :
    let _ : Algebra (Place.integralClosureAt L v)
        (Place.placeOfPrime P).toValuationSubring :=
      finitePrimeValuationAlgebra (k := k) (K := K) (L := L) v P
    decompositionValuationEquiv (Place.placeOfPrime P) σ
        (algebraMap (Place.integralClosureAt L v) (Place.placeOfPrime P).toValuationSubring b) =
      algebraMap (Place.integralClosureAt L v) (Place.placeOfPrime P).toValuationSubring
        (σ.val • b) := by
  intro aBR
  let B := Place.integralClosureAt L v
  let R := (Place.placeOfPrime P).toValuationSubring
  have : IsScalarTower B R L :=
    finitePrimeValuationTower (k := k) (K := K) (L := L) v P
  apply Subtype.ext
  rw [decompositionValuationEquiv_coe]
  change σ.val (algebraMap R L (algebraMap B R b)) =
    algebraMap R L (algebraMap B R (σ.val • b))
  rw [← IsScalarTower.algebraMap_apply B R L,
    ← IsScalarTower.algebraMap_apply B R L]
  exact (algebraMap_galRestrict_apply v.toValuationSubring σ.val b).symm

/-- For the literal extending place, the original residue-action kernel
is the original ideal-inertia condition at the finite normalization prime. -/
theorem decompositionResidueAut_mem_ker_iff_normalizationInertia
    (P : HeightOneSpectrum (Place.integralClosureAt L v))
    (σ : decompositionGroup (K := K) (Place.placeOfPrime P)) :
    σ ∈ (decompositionResidueAut (K := K) (Place.placeOfPrime P)).ker ↔
      σ.val ∈ P.asIdeal.inertia Gal(L/K) := by
  let B := Place.integralClosureAt L v
  let R := (Place.placeOfPrime P).toValuationSubring
  let _ : Algebra B R :=
    finitePrimeValuationAlgebra (k := k) (K := K) (L := L) v P
  have : IsScalarTower B R L :=
    finitePrimeValuationTower (k := k) (K := K) (L := L) v P
  have : IsLocalization.AtPrime R P.asIdeal :=
    finitePrimeValuationLocalization (k := k) (K := K) (L := L) v P
  constructor
  · intro hσ b
    have hres := DFunLike.congr_fun (MonoidHom.mem_ker.mp hσ)
      (IsLocalRing.residue R (algebraMap B R b))
    change decompositionResidueAut (K := K) (Place.placeOfPrime P) σ
      (IsLocalRing.residue R (algebraMap B R b)) =
        IsLocalRing.residue R (algebraMap B R b) at hres
    rw [decompositionResidueAut_residue,
      decompositionValuationEquiv_normalization_algebraMap
        (k := k) (K := K) (L := L) v P σ b] at hres
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff R P.asIdeal (σ.val • b - b)).mp
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [map_sub, map_sub]
    exact sub_eq_zero.mpr hres
  · intro hσ
    have hres :
        (IsLocalRing.residue R).comp
          (decompositionValuationEquiv (Place.placeOfPrime P) σ).toRingHom =
        IsLocalRing.residue R := by
      apply IsLocalization.ringHom_ext P.asIdeal.primeCompl
      apply RingHom.ext
      intro b
      change IsLocalRing.residue R
          (decompositionValuationEquiv (Place.placeOfPrime P) σ (algebraMap B R b)) =
        IsLocalRing.residue R (algebraMap B R b)
      rw [decompositionValuationEquiv_normalization_algebraMap
        (k := k) (K := K) (L := L) v P σ b]
      apply sub_eq_zero.mp
      rw [← map_sub, ← map_sub]
      exact (IsLocalRing.residue_eq_zero_iff _).mpr
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff R P.asIdeal (σ.val • b - b)).mpr
          (hσ b))
    apply MonoidHom.mem_ker.mpr
    apply AlgEquiv.ext
    intro x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    change decompositionResidueAut (K := K) (Place.placeOfPrime P) σ
      (IsLocalRing.residue R r) = IsLocalRing.residue R r
    rw [decompositionResidueAut_residue]
    exact DFunLike.congr_fun hres r

/-- Including the actual residue inertia in the finite Galois group gives
the literal normalization inertia subgroup at the same prime. -/
theorem decompositionResidueKer_map_eq_normalizationInertia
    (P : HeightOneSpectrum (Place.integralClosureAt L v)) :
    (decompositionResidueAut (K := K) (Place.placeOfPrime P)).ker.map
        (decompositionGroup (K := K) (Place.placeOfPrime P)).subtype =
      P.asIdeal.inertia Gal(L/K) := by
  apply Subgroup.ext
  intro σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact (decompositionResidueAut_mem_ker_iff_normalizationInertia v P τ).mp hτ
  · intro hσ
    let τ : decompositionGroup (K := K) (Place.placeOfPrime P) :=
      ⟨σ, (Place.placeOfPrime_stabilizer_iff v P σ).mp
        (P.asIdeal.inertia_le_stabilizer hσ)⟩
    exact ⟨τ, (decompositionResidueAut_mem_ker_iff_normalizationInertia v P τ).mpr hσ, rfl⟩

end FiniteNormalization

end IdeleGroup

section Absolute

attribute [local instance] normalizationInertiaImageAction

variable {k : Type u} {K : Type v} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K]

attribute [local instance] placeAmbientAlgebra placeAmbientTower placeStageAmbientTower

/-- The literal original normalization inertia, mapped into the actual
absolute topological abelianization. -/
def placeAbsoluteInertia (v : Place k K)
    (Q : Ideal (integralClosure v.toValuationSubring (SeparableClosure K))) :
    Subgroup (localAbsoluteAbelianProfinite K) :=
  (Q.inertia Gal(SeparableClosure K/K)).map (localAbsoluteAbelianizationQuotientMap K)

omit [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] [HasPrincipalDivisors k K] in
/-- Original absolute inertia has compact image under the actual
topological abelianization quotient map. -/
theorem isCompact_placeAbsoluteInertia (v : Place k K)
    (Q : Ideal (integralClosure v.toValuationSubring (SeparableClosure K))) :
    IsCompact (placeAbsoluteInertia v Q : Set (localAbsoluteAbelianProfinite K)) :=
  (actualNormalizationInertia_isClosed v.toValuationSubring K
    (SeparableClosure K) Q).isCompact.image QuotientGroup.continuous_mk

omit [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] [HasPrincipalDivisors k K] in
/-- At every finite abelian field, original absolute inertia restricts
onto the inertia of the literal contracted normalization prime. -/
theorem placeAbsoluteInertia_restriction (v : Place k K)
    (Q : Ideal (integralClosure v.toValuationSubring (SeparableClosure K)))
    [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring)]
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    (placeAbsoluteInertia v Q).map (absoluteAbelianRestriction K E).toMonoidHom =
      (placeAbsolutePrimeAt v Q E).asIdeal.inertia Gal(E/K) := by
  have hprojection :
      (absoluteAbelianRestriction K E).toMonoidHom.comp
        (localAbsoluteAbelianizationQuotientMap K) = AlgEquiv.restrictNormalHom E := by
    apply MonoidHom.ext
    intro σ
    exact absoluteAbelianRestriction_mk K E σ
  rw [placeAbsoluteInertia, Subgroup.map_map, hprojection]
  let E' : FiniteGaloisIntermediateField K (SeparableClosure K) :=
    { toIntermediateField := E
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  exact integralClosure_inertia_map_eq_finiteGalois_contraction
    v.toValuationSubring K (SeparableClosure K) E' Q

namespace RayClass

/-- Every original higher-unit image is compact, since the higher units
are closed in the compact ordinary-unit subgroup of the local field. -/
theorem isCompact_placeArtinUnitImage (v : Place k K) (n : ℕ) :
    IsCompact (placeArtinUnitImage v n : Set (localAbsoluteAbelianProfinite K)) := by
  have hU : IsCompact (localHigherUnitGroup v n : Set v.adicCompletionˣ) :=
    (FunctionField.isCompact_localUnits v).of_isClosed_subset
      ((localHigherUnitGroup v n).isClosed_of_isOpen (isOpen_localHigherUnitGroup v n))
      (localHigherUnitGroup_le_localUnits v n)
  exact hU.image ((absoluteArtin k K).continuous_toFun.comp
    (QuotientGroup.continuous_mk.comp (IdeleGroup.continuous_placeIdele v)))

/-- Restricting the original local ordinary-unit image to a finite
abelian extension gives its literal normalization inertia subgroup. -/
theorem placeArtinUnitImage_zero_restriction (v : Place k K)
    (Q : Ideal (integralClosure v.toValuationSubring (SeparableClosure K)))
    [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring)]
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    (placeArtinUnitImage v 0).map (absoluteAbelianRestriction K E).toMonoidHom =
      (placeAbsolutePrimeAt v Q E).asIdeal.inertia Gal(E/K) := by
  let _ : Algebra k (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
  have : IsScalarTower k K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : HasPrincipalDivisors k E :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K E).toHasPrincipalDivisors
  let presentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K E
  let _ : Algebra (RatFunc k) E := presentation.val
  have : IsScalarTower k (RatFunc k) E := presentation.property.1
  have : FunctionField k E := presentation.property.2
  have hfinite :
      (placeArtinUnitImage v 0).map (absoluteAbelianRestriction K E).toMonoidHom =
        (localHigherUnitGroup v 0).map ((abelianFiniteArtin k K E).comp
          ((IdeleClassGroup.mk (k := k) (K := K)).comp (IdeleGroup.placeIdele v))) := by
    apply Subgroup.ext
    intro τ
    constructor
    · rintro ⟨a, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (absoluteArtin_restriction k K E
        (IdeleClassGroup.mk (IdeleGroup.placeIdele v x))).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨placeAbsoluteArtin v x, ⟨x, hx, rfl⟩,
        absoluteArtin_restriction k K E (IdeleClassGroup.mk (IdeleGroup.placeIdele v x))⟩
  rw [hfinite]
  have hUnits :
      (localHigherUnitGroup v 0).map ((abelianFiniteArtin k K E).comp
        ((IdeleClassGroup.mk (k := k) (K := K)).comp (IdeleGroup.placeIdele v))) =
      (IdeleGroup.decompositionResidueAut (K := K)
        (Place.placeOfPrime (placeAbsolutePrimeAt v Q E))).ker.map
          (IdeleGroup.decompositionGroup (K := K)
            (Place.placeOfPrime (placeAbsolutePrimeAt v Q E))).subtype := by
    have hrestrict : (Place.placeOfPrime (placeAbsolutePrimeAt v Q E)).restrict K = v :=
      Place.restrict_placeOfPrime (placeAbsolutePrimeAt v Q E)
    have htransport := congrArg (fun u : Place k K =>
      (localHigherUnitGroup u 0).map ((abelianFiniteArtin k K E).comp
        ((IdeleClassGroup.mk (k := k) (K := K)).comp (IdeleGroup.placeIdele u)))) hrestrict
    exact htransport.symm.trans
      (abelianFiniteArtin_placeIdele_units (K := K)
        (Place.placeOfPrime (placeAbsolutePrimeAt v Q E)))
  exact hUnits.trans
    (IdeleGroup.decompositionResidueKer_map_eq_normalizationInertia v (placeAbsolutePrimeAt v Q E))

/-- The original normalization inertia image is exactly the original
ordinary-unit Artin image, before imposing any ray quotient. -/
theorem placeAbsoluteInertia_eq_placeArtinUnitImage (v : Place k K)
    (Q : Ideal (integralClosure v.toValuationSubring (SeparableClosure K)))
    [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring)] :
    placeAbsoluteInertia v Q = placeArtinUnitImage v 0 := by
  let I := placeAbsoluteInertia v Q
  let U := placeArtinUnitImage v 0
  change I = U
  have hI : IsClosed (I : Set (localAbsoluteAbelianProfinite K)) :=
    (isCompact_placeAbsoluteInertia v Q).isClosed
  have hU : IsClosed (U : Set (localAbsoluteAbelianProfinite K)) :=
    (isCompact_placeArtinUnitImage v 0).isClosed
  have hfinite : ∀ N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K),
      I.map (QuotientGroup.mk' N.toSubgroup) = U.map (QuotientGroup.mk' N.toSubgroup) := by
    intro N
    let E := absoluteFiniteQuotientField K N
    let e : localAbsoluteAbelianProfinite K ⧸ N.toSubgroup ≃* Gal(E/K) :=
      (absoluteFiniteQuotientEquiv K N).toMulEquiv
    have hrestriction : I.map (absoluteAbelianRestriction K E).toMonoidHom =
        U.map (absoluteAbelianRestriction K E).toMonoidHom :=
      (placeAbsoluteInertia_restriction v Q E).trans
        (placeArtinUnitImage_zero_restriction v Q E).symm
    have hprojection : e.symm.toMonoidHom.comp (absoluteAbelianRestriction K E).toMonoidHom =
        QuotientGroup.mk' N.toSubgroup := by
      apply MonoidHom.ext
      intro a
      apply e.injective
      change e (e.symm (absoluteAbelianRestriction K E a)) = e (QuotientGroup.mk a)
      rw [e.apply_symm_apply]
      exact absoluteRestriction_eq_finiteQuotient N a
    have h := congrArg (fun S : Subgroup Gal(E/K) => S.map e.symm.toMonoidHom) hrestriction
    simpa only [Subgroup.map_map, hprojection] using h
  apply le_antisymm
  · intro a ha
    have hclosure : a ∈ U.topologicalClosure :=
      mem_subgroupClosure_of_all_finite_images U a (fun N => by
        rw [← hfinite N]
        exact ⟨a, ha, rfl⟩)
    change a ∈ closure (U : Set (localAbsoluteAbelianProfinite K)) at hclosure
    rwa [hU.closure_eq] at hclosure
  · intro a ha
    have hclosure : a ∈ I.topologicalClosure :=
      mem_subgroupClosure_of_all_finite_images I a (fun N => by
        rw [hfinite N]
        exact ⟨a, ha, rfl⟩)
    change a ∈ closure (I : Set (localAbsoluteAbelianProfinite K)) at hclosure
    rwa [hI.closure_eq] at hclosure

end RayClass

end Absolute

end FunctionField

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayEmbedding
public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationDecompositionClosed
public import Nyll.AlgebraicCurves.Places.Ramification.PlaceFiberCenterEquivariance
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteRestriction
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GlobalDecomposition
public import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteNormalizationPrime
public import Nyll.ProCGroups.Profinite.OpenSubgroups
public import Nyll.SchemeTheory.RingTheory.Ramification.ProfiniteInertiaMap
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve

/-!
# Native decomposition and the original one-place reciprocity image

The actual stabilizer of a prime in the normalization of the base valuation
ring restricts onto the stabilizer of its literal prime at every finite
Galois stage. The place associated with that prime identifies this group
with the decomposition group used by local reciprocity. Finite abelian
restrictions then identify the native absolute decomposition image with
the closure of the original one-place Artin image.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicCurve LocalClassFieldTheory
open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

attribute [local instance] normalizationCommAlgGaloisAction

section FiniteRestriction

attribute [local instance] normalizationInertiaImageAction

variable (A K Ω : Type*) [CommRing A] [Field K] [Field Ω]
    [Algebra A K] [IsFractionRing A K] [Algebra K Ω] [Algebra A Ω]
    [IsScalarTower A K Ω] [IsGalois K Ω]

/-- The normalization stage uses the scalar tower inherited from its ambient field. -/
local instance normalizationStageTower (E : IntermediateField K Ω) :
    IsScalarTower A E Ω :=
  Subalgebra.isScalarTower_mid (S := E.toSubalgebra) (α := A) (β := Ω)

/-- The stage normalization uses the canonical Galois action on its integral closure. -/
local instance normalizationStageAction (E : IntermediateField K Ω)
    [IsGalois K E] : MulSemiringAction Gal(E/K) (integralClosure A E) :=
  normalizationInertiaImageAction A K E

/-- Restriction of the original normalization-prime stabilizer is the
entire stabilizer of the literal contracted prime. -/
theorem normalizationDecomposition_map_restrictNormal
    (E : IntermediateField K Ω) [IsGalois K E]
    (Q : Ideal (integralClosure A Ω)) [Q.IsPrime] :
    let stageAction : MulSemiringAction Gal(E/K) (integralClosure A E) :=
      normalizationInertiaImageAction A K E
    let : MulAction Gal(E/K) (Ideal (integralClosure A E)) :=
      (@Ideal.pointwiseDistribMulAction Gal(E/K) (integralClosure A E)
        inferInstance inferInstance stageAction).toMulAction
    (MulAction.stabilizer Gal(Ω/K) Q).map (AlgEquiv.restrictNormalHom E) =
      MulAction.stabilizer Gal(E/K)
        (Q.comap (IsScalarTower.toAlgHom A E Ω).mapIntegralClosure) := by
  intro stageAction stageIdealAction
  let : Algebra (integralClosure A E) (integralClosure A Ω) :=
    (IsScalarTower.toAlgHom A E Ω).mapIntegralClosure.toRingHom.toAlgebra
  let : TopologicalSpace (integralClosure A Ω) := ⊥
  have : DiscreteTopology (integralClosure A Ω) := ⟨rfl⟩
  have : ContinuousSMul Gal(Ω/K) (integralClosure A Ω) :=
    integralClosure_continuousSMul_krull A K Ω
  have : CompactSpace E.fixingSubgroup :=
    isCompact_iff_compactSpace.mp (InfiniteGalois.fixingSubgroup_isClosed E).isCompact
  have : Algebra.IsInvariant (integralClosure A E) (integralClosure A Ω)
      E.fixingSubgroup := by
    constructor
    intro b hb
    have hbE : (b : Ω) ∈ E := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup E]
      apply (IntermediateField.mem_fixedField_iff E.fixingSubgroup (b : Ω)).mpr
      intro σ hσ
      have h := hb ⟨σ, hσ⟩
      change galRestrict A K Ω (integralClosure A Ω) σ b = b at h
      exact (algebraMap_galRestrict_apply A σ b).symm.trans (congrArg Subtype.val h)
    let e : E := ⟨(b : Ω), hbE⟩
    have he : IsIntegral A e :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom A E Ω)
        (algebraMap E Ω).injective).mp b.property
    refine ⟨⟨e, he⟩, ?_⟩
    apply Subtype.ext
    rfl
  have hker : E.fixingSubgroup ≤
      (AlgEquiv.restrictNormalHom E : Gal(Ω/K) →* Gal(E/K)).ker :=
    (IntermediateField.restrictNormalHom_ker E).ge
  have hcoeff : ∀ (σ : Gal(Ω/K)) (b : integralClosure A E),
      algebraMap (integralClosure A E) (integralClosure A Ω)
          (AlgEquiv.restrictNormalHom E σ • b) =
        σ • algebraMap (integralClosure A E) (integralClosure A Ω) b := by
    intro σ b
    apply Subtype.ext
    change algebraMap E Ω
        (algebraMap (integralClosure A E) E
          (galRestrict A K E (integralClosure A E) (AlgEquiv.restrictNormalHom E σ) b)) =
      algebraMap (integralClosure A Ω) Ω
        (galRestrict A K Ω (integralClosure A Ω) σ
          ((IsScalarTower.toAlgHom A E Ω).mapIntegralClosure b))
    rw [algebraMap_galRestrict_apply A, algebraMap_galRestrict_apply A]
    exact AlgEquiv.restrictNormal_commutes σ E (algebraMap (integralClosure A E) E b)
  exact SchemeTheory.map_stabilizer_of_surjective_of_profinite
    (AlgEquiv.restrictNormalHom E) E.fixingSubgroup
    (Q.under (integralClosure A E)) Q
    (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) Ω) hker hcoeff

end FiniteRestriction

end EtaleFundamentalGroups.Inertia

namespace FunctionField

open EtaleFundamentalGroups.Inertia

/-- Finite continuous quotient images detect membership in a subgroup's closure. -/
theorem mem_subgroupClosure_of_all_finite_images
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (H : Subgroup G) (g : G)
    (h : ∀ N : OpenNormalSubgroup G,
      QuotientGroup.mk' N.toSubgroup g ∈ H.map (QuotientGroup.mk' N.toSubgroup)) :
    g ∈ H.topologicalClosure := by
  change g ∈ closure (H : Set G)
  by_contra hg
  let W : Set G := (fun x : G => x * g) ⁻¹' (closure (H : Set G))ᶜ
  have hW : IsOpen W :=
    isClosed_closure.isOpen_compl.preimage (continuous_id.mul continuous_const)
  have h1W : (1 : G) ∈ W := by
    change 1 * g ∉ closure (H : Set G)
    rw [one_mul]
    exact hg
  obtain ⟨N, hNW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW h1W
  obtain ⟨x, hx, hxg⟩ := h N
  have hdiv : x / g ∈ N.toSubgroup := QuotientGroup.eq_iff_div_mem.mp hxg
  have hnot := hNW hdiv
  change (x / g) * g ∉ closure (H : Set G) at hnot
  rw [div_mul_cancel] at hnot
  exact hnot (subset_closure hx)

section Absolute

variable {k : Type u} {K : Type v} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K]

/-- The base valuation ring acts on the ambient closure through its inclusion. -/
local instance placeAmbientAlgebra (v : Place k K) :
    Algebra v.toValuationSubring (SeparableClosure K) :=
  Algebra.ofSubsemiring v.toValuationSubring

/-- The ambient valuation-ring algebra factors through the original field. -/
local instance placeAmbientTower (v : Place k K) :
    IsScalarTower v.toValuationSubring K (SeparableClosure K) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- Each finite stage inherits the ambient valuation-ring scalar tower. -/
local instance placeStageAmbientTower (v : Place k K)
    (E : IntermediateField K (SeparableClosure K)) :
    IsScalarTower v.toValuationSubring E (SeparableClosure K) :=
  Subalgebra.isScalarTower_mid (S := E.toSubalgebra)
    (α := v.toValuationSubring) (β := SeparableClosure K)

attribute [local instance] normalizationCommAlgGaloisAction

/-- The actual absolute reciprocity homomorphism on one local multiplicative group. -/
def placeAbsoluteArtin (v : Place k K) :
    v.adicCompletionˣ →* localAbsoluteAbelianProfinite K :=
  (absoluteArtin k K).toMonoidHom.comp
    ((IdeleClassGroup.mk (k := k) (K := K)).comp (IdeleGroup.placeIdele v))

/-- The original normalization decomposition inclusion, mapped to the
actual absolute topological abelianization. -/
def placeAbsoluteDecomposition (v : Place k K)
    (Q : Ideal (integralClosure v.toValuationSubring (SeparableClosure K))) :
    Subgroup (localAbsoluteAbelianProfinite K) :=
  ((localAbsoluteAbelianizationQuotientMap K).comp
    (normalizationDecompositionInclusion v.toValuationSubring K (SeparableClosure K) Q)).range

omit [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] [HasPrincipalDivisors k K] in
/-- The native absolute decomposition image is compact with its literal range. -/
theorem isCompact_placeAbsoluteDecomposition (v : Place k K)
    (Q : Ideal (integralClosure v.toValuationSubring (SeparableClosure K))) :
    IsCompact (placeAbsoluteDecomposition v Q : Set (localAbsoluteAbelianProfinite K)) := by
  let q : Gal(SeparableClosure K/K) →ₜ* localAbsoluteAbelianProfinite K :=
    { localAbsoluteAbelianizationQuotientMap K with
      continuous_toFun := QuotientGroup.continuous_mk }
  exact normalizationDecompositionImage_isCompact v.toValuationSubring K
    (SeparableClosure K) Q q

/-- The literal finite contraction of the same absolute prime, regarded as
the height-one prime that supplies its actual extending place. -/
def placeAbsolutePrimeAt (v : Place k K)
    (Q : Ideal (integralClosure v.toValuationSubring (SeparableClosure K)))
    [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring)]
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsGalois K E] :
    IsDedekindDomain.HeightOneSpectrum (Place.integralClosureAt E v) := by
  let P := absoluteNormalizationPrimeContraction
    (A := v.toValuationSubring) (L := E) (Omega := SeparableClosure K) Q
  refine ⟨P, inferInstance, ?_⟩
  intro hP
  have hbase := (inferInstance : P.LiesOver
    (IsLocalRing.maximalIdeal v.toValuationSubring)).over
  rw [hP, Ideal.under_def, Ideal.comap_bot_of_injective _
    (Place.algebraMap_integralClosureAt_injective v)] at hbase
  exact Place.maximalIdeal_ne_bot v hbase

omit [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] [HasPrincipalDivisors k K] in
/-- Every finite abelian restriction of the native decomposition image is
the original decomposition group of the place at the contracted prime. -/
theorem placeAbsoluteDecomposition_restriction (v : Place k K)
    (Q : Ideal (integralClosure v.toValuationSubring (SeparableClosure K)))
    [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring)]
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    (placeAbsoluteDecomposition v Q).map (absoluteAbelianRestriction K E).toMonoidHom =
      IdeleGroup.decompositionGroup (K := K) (Place.placeOfPrime (placeAbsolutePrimeAt v Q E)) := by
  intro akΩ hkKΩ
  let upperAction : MulSemiringAction Gal(SeparableClosure K/K)
      (integralClosure v.toValuationSubring (SeparableClosure K)) :=
    normalizationInertiaImageAction v.toValuationSubring K (SeparableClosure K)
  let upperIdealAction : MulAction Gal(SeparableClosure K/K)
      (Ideal (integralClosure v.toValuationSubring (SeparableClosure K))) :=
    (@Ideal.pointwiseDistribMulAction Gal(SeparableClosure K/K)
      (integralClosure v.toValuationSubring (SeparableClosure K))
      inferInstance inferInstance upperAction).toMulAction
  have hmap :
      (placeAbsoluteDecomposition v Q).map (absoluteAbelianRestriction K E).toMonoidHom =
        (MulAction.stabilizer Gal(SeparableClosure K/K) Q).map
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := SeparableClosure K) E) := by
    apply Subgroup.ext
    intro τ
    constructor
    · rintro ⟨a, ⟨d, rfl⟩, rfl⟩
      exact ⟨d.val, d.property, (absoluteAbelianRestriction_mk K E d.val).symm⟩
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨localAbsoluteAbelianizationQuotientMap K σ, ⟨⟨σ, hσ⟩, rfl⟩,
        absoluteAbelianRestriction_mk K E σ⟩
  let stageAction : MulSemiringAction Gal(E/K) (integralClosure v.toValuationSubring E) :=
    normalizationInertiaImageAction v.toValuationSubring K E
  let stageIdealAction : MulAction Gal(E/K) (Ideal (integralClosure v.toValuationSubring E)) :=
    (@Ideal.pointwiseDistribMulAction Gal(E/K) (integralClosure v.toValuationSubring E)
      inferInstance inferInstance stageAction).toMulAction
  have hrestriction :
      (MulAction.stabilizer Gal(SeparableClosure K/K) Q).map
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := SeparableClosure K) E) =
        MulAction.stabilizer Gal(E/K)
          (Q.comap (IsScalarTower.toAlgHom v.toValuationSubring E
            (SeparableClosure K)).mapIntegralClosure) :=
    normalizationDecomposition_map_restrictNormal
      v.toValuationSubring K (SeparableClosure K) E Q
  refine hmap.trans (hrestriction.trans ?_)
  apply Subgroup.ext
  intro σ
  exact Place.placeOfPrime_stabilizer_iff v (placeAbsolutePrimeAt v Q E) σ

/-- The same finite restriction of the original one-place Artin image is
that same actual decomposition group; no compatibility equality is assumed. -/
theorem placeAbsoluteArtin_restriction_range (v : Place k K)
    (Q : Ideal (integralClosure v.toValuationSubring (SeparableClosure K)))
    [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring)]
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    (placeAbsoluteArtin v).range.map (absoluteAbelianRestriction K E).toMonoidHom =
      IdeleGroup.decompositionGroup (K := K) (Place.placeOfPrime (placeAbsolutePrimeAt v Q E)) := by
  intro akΩ hkKΩ
  let aRΩ : Algebra (RatFunc k) (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
  have hRKΩ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRΩ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun a => congrArg (algebraMap K (SeparableClosure K))
      (IsScalarTower.algebraMap_apply k (RatFunc k) K a))
  have : HasPrincipalDivisors k E :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K E).toHasPrincipalDivisors
  have hfinite :
      (placeAbsoluteArtin v).range.map (absoluteAbelianRestriction K E).toMonoidHom =
        ((abelianFiniteArtin k K E).comp
          ((IdeleClassGroup.mk (k := k) (K := K)).comp (IdeleGroup.placeIdele v))).range := by
    apply Subgroup.ext
    intro τ
    constructor
    · rintro ⟨a, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, (absoluteArtin_restriction k K E
        (IdeleClassGroup.mk (IdeleGroup.placeIdele v x))).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨placeAbsoluteArtin v x, ⟨x, rfl⟩,
        absoluteArtin_restriction k K E (IdeleClassGroup.mk (IdeleGroup.placeIdele v x))⟩
  rw [hfinite]
  let w := Place.placeOfPrime (placeAbsolutePrimeAt v Q E)
  have hrestrict : w.restrict K = v := Place.restrict_placeOfPrime (placeAbsolutePrimeAt v Q E)
  have hlocal := abelianFiniteArtin_placeIdele_range (k := k) (K := K) (L := E) w
  have htransport := congrArg (fun z : Place k K =>
    ((abelianFiniteArtin k K E).comp
      ((IdeleClassGroup.mk (k := k) (K := K)).comp (IdeleGroup.placeIdele z))).range) hrestrict
  exact htransport.symm.trans hlocal

/-- Restriction to the field of a finite abelian quotient is the original
quotient projection followed by its concrete Galois equivalence. -/
theorem absoluteRestriction_eq_finiteQuotient
    (N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K))
    (a : localAbsoluteAbelianProfinite K) :
    absoluteAbelianRestriction K (absoluteFiniteQuotientField K N) a =
      absoluteFiniteQuotientEquiv K N (QuotientGroup.mk a) := by
  refine QuotientGroup.induction_on a fun σ => ?_
  rw [absoluteAbelianRestriction_mk, absoluteFiniteQuotientEquiv_mk_mk]

/-- The closure of the original local Artin image is the literal image of
the original absolute normalization decomposition group. -/
theorem placeAbsoluteArtin_closure_eq_decomposition (v : Place k K)
    (Q : Ideal (integralClosure v.toValuationSubring (SeparableClosure K)))
    [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring)] :
    (placeAbsoluteArtin v).range.topologicalClosure = placeAbsoluteDecomposition v Q := by
  let H := (placeAbsoluteArtin v).range
  let D := placeAbsoluteDecomposition v Q
  change H.topologicalClosure = D
  have hD : IsClosed (D : Set (localAbsoluteAbelianProfinite K)) :=
    (isCompact_placeAbsoluteDecomposition v Q).isClosed
  have hfinite : ∀ N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K),
      H.map (QuotientGroup.mk' N.toSubgroup) = D.map (QuotientGroup.mk' N.toSubgroup) := by
    intro N
    let E := absoluteFiniteQuotientField K N
    let e : localAbsoluteAbelianProfinite K ⧸ N.toSubgroup ≃* Gal(E/K) :=
      (absoluteFiniteQuotientEquiv K N).toMulEquiv
    have hrestriction : H.map (absoluteAbelianRestriction K E).toMonoidHom =
        D.map (absoluteAbelianRestriction K E).toMonoidHom :=
      (placeAbsoluteArtin_restriction_range v Q E).trans
        (placeAbsoluteDecomposition_restriction v Q E).symm
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
  have hHD : H ≤ D := by
    intro a ha
    have hclosure : a ∈ D.topologicalClosure :=
      mem_subgroupClosure_of_all_finite_images D a (fun N => by
        rw [← hfinite N]
        exact ⟨a, ha, rfl⟩)
    change a ∈ closure (D : Set (localAbsoluteAbelianProfinite K)) at hclosure
    rwa [hD.closure_eq] at hclosure
  apply le_antisymm
  · exact H.topologicalClosure_minimal hHD hD
  · intro a ha
    apply mem_subgroupClosure_of_all_finite_images H a
    intro N
    rw [hfinite N]
    exact ⟨a, ha, rfl⟩

namespace RayClass

/-- In the actual ray-Artin quotient, the closure of the original local
factor is the image of the original normalization decomposition inclusion. -/
theorem localRayAbsoluteArtin_closure_eq_decomposition
    (m : Modulus k K) (v : Place k K)
    (Q : Ideal (integralClosure v.toValuationSubring (SeparableClosure K)))
    [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring)] :
    (localRayAbsoluteArtin m v).range.topologicalClosure =
      (((QuotientGroup.mk' (artinRaySubgroup m)).comp
        (localAbsoluteAbelianizationQuotientMap K)).comp
          (normalizationDecompositionInclusion v.toValuationSubring K
            (SeparableClosure K) Q)).range := by
  have : IsClosed (artinRaySubgroup m : Set (localAbsoluteAbelianProfinite K)) :=
    isClosed_artinRaySubgroup m
  let q : localAbsoluteAbelianProfinite K →*
      localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m :=
    QuotientGroup.mk' (artinRaySubgroup m)
  let π : Gal(SeparableClosure K/K) →ₜ*
      localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m :=
    { q.comp (localAbsoluteAbelianizationQuotientMap K) with
      continuous_toFun := QuotientGroup.continuous_mk.comp QuotientGroup.continuous_mk }
  let D := (π.toMonoidHom.comp
    (normalizationDecompositionInclusion v.toValuationSubring K (SeparableClosure K) Q)).range
  let R := (localRayAbsoluteArtin m v).range
  change R.topologicalClosure = D
  have hD : IsClosed (D : Set (localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m)) :=
    (normalizationDecompositionImage_isCompact v.toValuationSubring K
      (SeparableClosure K) Q π).isClosed
  have hmap : D = (placeAbsoluteDecomposition v Q).map q := by
    apply Subgroup.ext
    intro g
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨localAbsoluteAbelianizationQuotientMap K d.val, ⟨d, rfl⟩, rfl⟩
    · rintro ⟨a, ⟨d, rfl⟩, rfl⟩
      exact ⟨d, rfl⟩
  have hlocal : (placeAbsoluteArtin v).range.map q = R := by
    apply Subgroup.ext
    intro g
    constructor
    · rintro ⟨a, ⟨x, rfl⟩, rfl⟩
      exact ⟨QuotientGroup.mk' (localHigherUnitGroup v (m v)) x,
        localRayAbsoluteArtin_mk m v x⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (localHigherUnitGroup v (m v)) a
      exact ⟨placeAbsoluteArtin v x, ⟨x, rfl⟩, (localRayAbsoluteArtin_mk m v x).symm⟩
  have hsource : (placeAbsoluteArtin v).range ≤ placeAbsoluteDecomposition v Q := by
    rw [← placeAbsoluteArtin_closure_eq_decomposition v Q]
    exact Subgroup.le_topologicalClosure _
  have hRD : R ≤ D := by
    rw [← hlocal, hmap]
    exact Subgroup.map_mono hsource
  apply le_antisymm
  · exact R.topologicalClosure_minimal hRD hD
  · have hpre : placeAbsoluteDecomposition v Q ≤ R.topologicalClosure.comap q := by
      rw [← placeAbsoluteArtin_closure_eq_decomposition v Q]
      apply (placeAbsoluteArtin v).range.topologicalClosure_minimal
      · intro a ha
        change q a ∈ R.topologicalClosure
        apply Subgroup.le_topologicalClosure R
        rw [← hlocal]
        exact ⟨a, ha, rfl⟩
      · exact (Subgroup.isClosed_topologicalClosure R).preimage QuotientGroup.continuous_mk
    intro g hg
    change g ∈ D at hg
    rw [hmap] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    exact hpre ha

end RayClass

end Absolute

end FunctionField

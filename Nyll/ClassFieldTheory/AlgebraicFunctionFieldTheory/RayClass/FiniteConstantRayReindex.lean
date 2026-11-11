/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayWildInertia
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteConstantDegreeReindex
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayDegree
public import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantExtension
public import Nyll.SchemeTheory.Normalization.NativeNormalizationPrime
public import Nyll.SchemeTheory.Normalization.SubalgebraPreimage

/-!
# Original ray quotients under finite enlargement of the constants

The existing constant-field equivalence of places leaves the actual
valuation ring unchanged. The same normalization prime therefore has the
same full inertia, wild inertia, and decomposition images in the original
absolute abelian group. Their proved local reciprocity descriptions identify
the native unit images and reduced ray subgroups over both constant fields.
The resulting ray-quotient comparison fixes every original representative.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve LocalClassFieldTheory EtaleFundamentalGroups.Inertia

namespace FunctionField.RayClass

section Moduli

variable (k E K : Type*) [Field k] [Field E] [Field K]
  [Algebra k E] [Algebra k K] [Algebra E K] [IsScalarTower k E K]
  [Algebra.IsIntegral k E]

/-- Reindex a modulus along the original equivalence that forgets finite
constants and keeps the literal valuation subrings. -/
def modulusForgetConstants (m : Modulus E K) : Modulus k K :=
  Finsupp.domCongr (Place.constantFieldEquiv k E).symm m

/-- The reindexed coefficient is the coefficient of the same place. -/
theorem modulusForgetConstants_apply (m : Modulus E K) (v : Place k K) :
    modulusForgetConstants k E K m v = m (v.extendConstants E) :=
  Finsupp.equivMapDomain_apply (Place.constantFieldEquiv k E).symm m v

/-- Forgetting constants preserves the coefficient at the original place. -/
theorem modulusForgetConstants_forgetConstants (m : Modulus E K) (v : Place E K) :
    modulusForgetConstants k E K m (v.forgetConstants (K := k)) = m v := by
  rw [modulusForgetConstants_apply]
  exact congrArg m ((Place.constantFieldEquiv k E).apply_symm_apply v)

/-- The same reduced boundary remains reduced after reindexing. -/
theorem modulusForgetConstants_reduced (m : Modulus E K) (hm : ∀ v, m v ≤ 1) :
    ∀ v, modulusForgetConstants k E K m v ≤ 1 := by
  intro v
  rw [modulusForgetConstants_apply]
  exact hm (v.extendConstants E)

end Moduli

variable (k E K : Type*) [Field k] [Finite k] [Field E] [Finite E] [Field K]
  [Algebra k E] [Algebra k K] [Algebra E K] [IsScalarTower k E K]
  [Algebra.IsIntegral k E]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [Algebra (RatFunc E) K] [IsScalarTower E (RatFunc E) K] [FunctionField E K]
  [HasPrincipalDivisors k K] [HasPrincipalDivisors E K]

attribute [local instance] normalizationCommAlgGaloisAction

omit [Algebra.IsIntegral k E] in
/-- Full ordinary units, full principal units, and the closed local
multiplicative image are unchanged when the finite constants are forgotten.
All three equalities use the same original normalization prime. -/
theorem placeArtinImages_forgetConstants (v : Place E K) :
    placeArtinUnitImage (v.forgetConstants (K := k)) 0 = placeArtinUnitImage v 0 ∧
    placeArtinUnitImage (v.forgetConstants (K := k)) 1 = placeArtinUnitImage v 1 ∧
    (placeAbsoluteArtin (v.forgetConstants (K := k))).range.topologicalClosure =
      (placeAbsoluteArtin v).range.topologicalClosure := by
  let : Algebra v.toValuationSubring (SeparableClosure K) :=
    Algebra.ofSubsemiring v.toValuationSubring
  have : IsScalarTower v.toValuationSubring K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Nontrivial
      (SchemeTheory.normalizationCommAlgCat v.toValuationSubring (SeparableClosure K)) :=
    (inferInstance : Nontrivial (integralClosure v.toValuationSubring (SeparableClosure K)))
  obtain ⟨Q, hQ⟩ := Ideal.exists_maximal
    (SchemeTheory.normalizationCommAlgCat v.toValuationSubring (SeparableClosure K)).carrier
  have hQover : Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring) :=
    SchemeTheory.normalizationCommAlgCat_liesOver_maximalIdeal Q
  refine ⟨?_, ?_, ?_⟩
  · exact (@placeAbsoluteInertia_eq_placeArtinUnitImage k K _ _ _ _ _ _ _ _
      (v.forgetConstants (K := k)) Q hQ.isPrime hQover).symm.trans
        (@placeAbsoluteInertia_eq_placeArtinUnitImage E K _ _ _ _ _ _ _ _ v Q hQ.isPrime hQover)
  · exact (@placeAbsoluteWild_eq_placeArtinUnitImage k K _ _ _ _ _ _ _ _
      (v.forgetConstants (K := k)) Q hQ.isPrime hQover).symm.trans
        (@placeAbsoluteWild_eq_placeArtinUnitImage E K _ _ _ _ _ _ _ _ v Q hQ.isPrime hQover)
  · exact (@placeAbsoluteArtin_closure_eq_decomposition k K _ _ _ _ _ _ _ _
      (v.forgetConstants (K := k)) Q hQ.isPrime hQover).trans
        (@placeAbsoluteArtin_closure_eq_decomposition E K _ _ _ _ _ _ _ _
          v Q hQ.isPrime hQover).symm

omit [Algebra.IsIntegral k E] in
/-- Every depth in a reduced modulus has the same original local Artin image. -/
theorem placeArtinUnitImage_forgetConstants_of_le_one
    (v : Place E K) (n : ℕ) (hn : n ≤ 1) :
    placeArtinUnitImage (v.forgetConstants (K := k)) n = placeArtinUnitImage v n := by
  have h := placeArtinImages_forgetConstants k E K v
  by_cases hz : n = 0
  · subst n
    exact h.1
  · have ho : n = 1 := by omega
    subst n
    exact h.2.1

/-- Reindexing a reduced boundary gives the same subgroup of the original
absolute abelian Galois group, before any quotient is formed. -/
theorem artinRaySubgroup_modulusForgetConstants
    (m : Modulus E K) (hm : ∀ v, m v ≤ 1) :
    artinRaySubgroup (modulusForgetConstants k E K m) = artinRaySubgroup m := by
  rw [artinRaySubgroup_eq_topologicalClosure_iSup, artinRaySubgroup_eq_topologicalClosure_iSup]
  apply congrArg Subgroup.topologicalClosure
  apply le_antisymm
  · apply iSup_le
    intro v
    rw [modulusForgetConstants_apply]
    have h := placeArtinUnitImage_forgetConstants_of_le_one k E K
      (v.extendConstants E) (m (v.extendConstants E)) (hm _)
    have hv : (v.extendConstants E).forgetConstants (K := k) = v := Place.ext rfl
    rw [hv] at h
    rw [h]
    exact le_iSup (fun w : Place E K => placeArtinUnitImage w (m w)) (v.extendConstants E)
  · apply iSup_le
    intro v
    apply le_iSup_of_le (v.forgetConstants (K := k))
    rw [modulusForgetConstants_forgetConstants]
    exact (placeArtinUnitImage_forgetConstants_of_le_one k E K v (m v) (hm v)).ge

/-- The original native ray quotients are identified through the proved
equality of their subgroups in the same absolute abelian group. -/
def rayForgetConstantsEquiv (m : Modulus E K) (hm : ∀ v, m v ≤ 1) :
    (localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup (modulusForgetConstants k E K m)) ≃*
      (localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m) :=
  QuotientGroup.quotientMulEquivOfEq (artinRaySubgroup_modulusForgetConstants k E K m hm)

/-- The comparison fixes every original absolute-abelian representative. -/
theorem rayForgetConstantsEquiv_mk
    (m : Modulus E K) (hm : ∀ v, m v ≤ 1) (a : localAbsoluteAbelianProfinite K) :
    rayForgetConstantsEquiv k E K m hm
        (QuotientGroup.mk' (artinRaySubgroup (modulusForgetConstants k E K m)) a) =
      QuotientGroup.mk' (artinRaySubgroup m) a :=
  QuotientGroup.quotientMulEquivOfEq_mk _ _

/-- Reindexing retains the original normalized arithmetic degree on
every element of the original native ray quotient. -/
theorem rayForgetConstantsEquiv_degree
    (m : Modulus E K) (hm : ∀ v, m v ≤ 1)
    (g : localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup (modulusForgetConstants k E K m)) :
    rayAbelianDegree m (rayForgetConstantsEquiv k E K m hm g) =
      rayAbelianDegree (modulusForgetConstants k E K m) g := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
    (artinRaySubgroup (modulusForgetConstants k E K m)) g
  rw [rayForgetConstantsEquiv_mk, rayAbelianDegree_mk, rayAbelianDegree_mk,
    absoluteAbelianDegree_forgetConstants k E K]

/-- The same native quotient comparison preserves the closure of each
original local image at its unchanged valuation ring. -/
theorem rayForgetConstantsEquiv_localClosure
    (m : Modulus E K) (hm : ∀ v, m v ≤ 1) (v : Place E K)
    (g : localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup (modulusForgetConstants k E K m)) :
    g ∈ (localRayAbsoluteArtin (modulusForgetConstants k E K m)
        (v.forgetConstants (K := k))).range.topologicalClosure ↔
      rayForgetConstantsEquiv k E K m hm g ∈
        (localRayAbsoluteArtin m v).range.topologicalClosure := by
  let : Algebra v.toValuationSubring (SeparableClosure K) :=
    Algebra.ofSubsemiring v.toValuationSubring
  have : IsScalarTower v.toValuationSubring K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Nontrivial
      (SchemeTheory.normalizationCommAlgCat v.toValuationSubring (SeparableClosure K)) :=
    (inferInstance : Nontrivial (integralClosure v.toValuationSubring (SeparableClosure K)))
  obtain ⟨Q, hQ⟩ := Ideal.exists_maximal
    (SchemeTheory.normalizationCommAlgCat v.toValuationSubring (SeparableClosure K)).carrier
  have hQover : Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring) :=
    SchemeTheory.normalizationCommAlgCat_liesOver_maximalIdeal Q
  rw [@localRayAbsoluteArtin_closure_eq_decomposition k K _ _ _ _ _ _ _ _
    (modulusForgetConstants k E K m) (v.forgetConstants (K := k)) Q hQ.isPrime hQover,
    @localRayAbsoluteArtin_closure_eq_decomposition E K _ _ _ _ _ _ _ _ m v Q hQ.isPrime hQover]
  constructor
  · rintro ⟨d, rfl⟩
    refine ⟨d, ?_⟩
    exact (rayForgetConstantsEquiv_mk k E K m hm
      (localAbsoluteAbelianizationQuotientMap K d.val)).symm
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    apply (rayForgetConstantsEquiv k E K m hm).injective
    exact (rayForgetConstantsEquiv_mk k E K m hm
      (localAbsoluteAbelianizationQuotientMap K d.val)).trans hd

end FunctionField.RayClass

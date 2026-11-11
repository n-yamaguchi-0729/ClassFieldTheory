/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalPrincipalWildImage
public import Nyll.EtaleFundamentalGroups.Inertia.ActualWildFieldImages
public import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationWildTopology
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.Ideal.GoingUp
public import Nyll.SchemeTheory.Normalization.SubalgebraPreimage

/-!
# Original wild inertia and the depth-one local Artin image

At every finite abelian restriction, the independently defined original
wild group and the actual principal units have the same image: both are
the characteristic-primary elements of the original finite inertia image.
Their compactness then identifies the two original subgroups of absolute
abelian Galois, before imposing a ray quotient.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicCurve LocalClassFieldTheory
open EtaleFundamentalGroups.Inertia

namespace FunctionField

attribute [local instance] normalizationCommAlgGaloisAction normalizationInertiaImageAction

variable {k : Type u} {K : Type v} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K]

attribute [local instance] placeAmbientAlgebra placeAmbientTower placeStageAmbientTower

omit [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] [HasPrincipalDivisors k K] in
private theorem rayWildPlacePrime_isMaximal (v : Place k K)
    (Q : Ideal (SchemeTheory.normalizationCommAlgCat v.toValuationSubring (SeparableClosure K)))
    [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring)] : Q.IsMaximal := by
  have : Algebra.IsIntegral v.toValuationSubring
      (SchemeTheory.normalizationCommAlgCat v.toValuationSubring (SeparableClosure K)) :=
    inferInstanceAs (Algebra.IsIntegral v.toValuationSubring
      (integralClosure v.toValuationSubring (SeparableClosure K)))
  exact Ideal.IsMaximal.of_liesOver_isMaximal Q (IsLocalRing.maximalIdeal v.toValuationSubring)

/-- The independently defined original normalization wild subgroup, mapped
through the original inertia inclusion and actual absolute abelianization. -/
def placeAbsoluteWild (v : Place k K)
    (Q : Ideal (SchemeTheory.normalizationCommAlgCat v.toValuationSubring (SeparableClosure K)))
    [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring)] :
    Subgroup (localAbsoluteAbelianProfinite K) := by
  have : Algebra.IsIntegral v.toValuationSubring
      (SchemeTheory.normalizationCommAlgCat v.toValuationSubring (SeparableClosure K)) :=
    inferInstanceAs (Algebra.IsIntegral v.toValuationSubring
      (integralClosure v.toValuationSubring (SeparableClosure K)))
  have : Q.IsMaximal :=
    Ideal.IsMaximal.of_liesOver_isMaximal Q (IsLocalRing.maximalIdeal v.toValuationSubring)
  exact (actualNormalizationWildSubgroup v.toValuationSubring K (SeparableClosure K) Q).map
    ((localAbsoluteAbelianizationQuotientMap K).comp
      (actualNormalizationInertiaInclusion v.toValuationSubring K
        (SeparableClosure K) Q).hom')

omit [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] [HasPrincipalDivisors k K] in
/-- The original wild image is compact in the original abelian Galois topology. -/
theorem isCompact_placeAbsoluteWild (v : Place k K)
    (Q : Ideal (SchemeTheory.normalizationCommAlgCat v.toValuationSubring (SeparableClosure K)))
    [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring)] :
    IsCompact (placeAbsoluteWild v Q : Set (localAbsoluteAbelianProfinite K)) := by
  have : Q.IsMaximal := rayWildPlacePrime_isMaximal v Q
  have : CompactSpace (actualNormalizationInertiaGroup v.toValuationSubring K
      (SeparableClosure K) Q).carrier :=
    actualNormalizationInertia_compactSpace v.toValuationSubring K (SeparableClosure K) Q
  exact (actualNormalizationWildSubgroup_isClosed v.toValuationSubring K
    (SeparableClosure K) Q).isCompact.image
      (QuotientGroup.continuous_mk.comp continuous_subtype_val)

omit [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] [HasPrincipalDivisors k K] in
/-- The actual finite abelian restriction of original wild inertia is the
characteristic-primary part of the literal finite normalization inertia. -/
theorem mem_placeAbsoluteWild_restriction_iff (v : Place k K)
    (Q : Ideal (SchemeTheory.normalizationCommAlgCat v.toValuationSubring (SeparableClosure K)))
    [hQprime : Q.IsPrime]
    [hQover : Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring)]
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] (g : Gal(E/K)) :
    have _ : (show Ideal (integralClosure v.toValuationSubring (SeparableClosure K))
      from Q).IsPrime := hQprime
    have _ : (show Ideal (integralClosure v.toValuationSubring (SeparableClosure K))
      from Q).LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring) := hQover
    g ∈ (placeAbsoluteWild v Q).map (absoluteAbelianRestriction K E).toMonoidHom ↔
      g ∈ (placeAbsolutePrimeAt v Q E).asIdeal.inertia Gal(E/K) ∧
        ∃ r : ℕ, g ^ ((ringChar k) ^ r) = 1 := by
  intro hQprimeRaw hQoverRaw
  have : Q.IsMaximal := rayWildPlacePrime_isMaximal v Q
  have hp : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
  have : CharP (IsLocalRing.ResidueField v.toValuationSubring) (ringChar k) :=
    CharP.of_ringHom_of_ne_zero
      ((IsLocalRing.residue v.toValuationSubring).comp (algebraMap k v.toValuationSubring))
      (ringChar k) hp.out.ne_zero
  let E' : FiniteGaloisIntermediateField K (SeparableClosure K) :=
    { toIntermediateField := E
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  have hab : (absoluteAbelianRestriction K E).toMonoidHom.comp
      (localAbsoluteAbelianizationQuotientMap K) = AlgEquiv.restrictNormalHom E := by
    apply MonoidHom.ext
    intro σ
    exact absoluteAbelianRestriction_mk K E σ
  have hinertia := placeAbsoluteInertia_restriction v Q E
  change (((show Ideal (integralClosure v.toValuationSubring (SeparableClosure K))
    from Q).inertia Gal(SeparableClosure K/K)).map
      (localAbsoluteAbelianizationQuotientMap K)).map
      (absoluteAbelianRestriction K E).toMonoidHom =
        (placeAbsolutePrimeAt v Q E).asIdeal.inertia Gal(E/K) at hinertia
  rw [Subgroup.map_map, hab] at hinertia
  have hprojection : (absoluteAbelianRestriction K E).toMonoidHom.comp
      ((localAbsoluteAbelianizationQuotientMap K).comp
        (actualNormalizationInertiaInclusion v.toValuationSubring K
          (SeparableClosure K) Q).hom') =
      (finiteGaloisRestrictionGroupMap K (SeparableClosure K) E').hom'.comp
        (actualNormalizationInertiaInclusion v.toValuationSubring K
          (SeparableClosure K) Q).hom' := by
    apply MonoidHom.ext
    intro σ
    exact absoluteAbelianRestriction_mk K E σ.val
  rw [placeAbsoluteWild, Subgroup.map_map, hprojection]
  exact (mem_actualNormalizationWildSubgroup_field_image_iff
    v.toValuationSubring K (SeparableClosure K) Q E' (ringChar k) g).trans
      (and_congr (Iff.of_eq (congrArg (fun S : Subgroup Gal(E/K) => g ∈ S) hinertia))
        Iff.rfl)

namespace RayClass

/-- At each actual finite abelian field, the original wild and principal-unit
images agree under the prescribed absolute restriction. -/
theorem placeAbsoluteWild_restriction (v : Place k K)
    (Q : Ideal (SchemeTheory.normalizationCommAlgCat v.toValuationSubring (SeparableClosure K)))
    [hQprime : Q.IsPrime]
    [hQover : Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring)]
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    (placeAbsoluteWild v Q).map (absoluteAbelianRestriction K E).toMonoidHom =
      (placeArtinUnitImage v 1).map (absoluteAbelianRestriction K E).toMonoidHom := by
  have hQprimeRaw : (show Ideal (integralClosure v.toValuationSubring (SeparableClosure K))
      from Q).IsPrime := hQprime
  have hQoverRaw : (show Ideal (integralClosure v.toValuationSubring (SeparableClosure K))
      from Q).LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring) := hQover
  apply Subgroup.ext
  intro g
  exact (mem_placeAbsoluteWild_restriction_iff v Q E g).trans
    (mem_placeArtinUnitImage_one_restriction_iff v Q E g).symm

/-- The original native normalization wild image is exactly the original
depth-one local Artin image, before taking any ray or affine quotient. -/
theorem placeAbsoluteWild_eq_placeArtinUnitImage (v : Place k K)
    (Q : Ideal (SchemeTheory.normalizationCommAlgCat v.toValuationSubring (SeparableClosure K)))
    [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring)] :
    placeAbsoluteWild v Q = placeArtinUnitImage v 1 := by
  let P := placeAbsoluteWild v Q
  let U := placeArtinUnitImage v 1
  change P = U
  have hP : IsClosed (P : Set (localAbsoluteAbelianProfinite K)) :=
    (isCompact_placeAbsoluteWild v Q).isClosed
  have hU : IsClosed (U : Set (localAbsoluteAbelianProfinite K)) :=
    (isCompact_placeArtinUnitImage v 1).isClosed
  have hfinite : ∀ N : OpenNormalSubgroup (localAbsoluteAbelianProfinite K),
      P.map (QuotientGroup.mk' N.toSubgroup) = U.map (QuotientGroup.mk' N.toSubgroup) := by
    intro N
    let E := absoluteFiniteQuotientField K N
    let e : localAbsoluteAbelianProfinite K ⧸ N.toSubgroup ≃* Gal(E/K) :=
      (absoluteFiniteQuotientEquiv K N).toMulEquiv
    have hrestriction : P.map (absoluteAbelianRestriction K E).toMonoidHom =
        U.map (absoluteAbelianRestriction K E).toMonoidHom :=
      placeAbsoluteWild_restriction v Q E
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
    have hclosure : a ∈ P.topologicalClosure :=
      mem_subgroupClosure_of_all_finite_images P a (fun N => by
        rw [hfinite N]
        exact ⟨a, ha, rfl⟩)
    change a ∈ closure (P : Set (localAbsoluteAbelianProfinite K)) at hclosure
    rwa [hP.closure_eq] at hclosure

end RayClass

end FunctionField

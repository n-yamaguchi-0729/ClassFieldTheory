/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayDecomposition

/-!
# Transport from the original normalization decomposition groups

The homomorphism used here is the original normalization decomposition
inclusion followed by the actual absolute abelianization and ray quotient.
Preserving its subgroup image supplies transport of original decomposition
representatives. The proved local reciprocity comparison then gives the
closed-local-image correspondence needed for multiplicative reconstruction.
No local multiplicative map or Artin compatibility square is an input.
-/

noncomputable section

open AlgebraicCurve LocalClassFieldTheory EtaleFundamentalGroups.Inertia

namespace FunctionField.RayClass

section NativeMap

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K]

private local instance normalizationAmbientAlgebra (v : Place k K) :
    Algebra v.toValuationSubring (SeparableClosure K) :=
  Algebra.ofSubsemiring v.toValuationSubring

private local instance normalizationAmbientTower (v : Place k K) :
    IsScalarTower v.toValuationSubring K (SeparableClosure K) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The original decomposition inclusion in the actual ray-Artin quotient. -/
def normalizationRayQuotientMap (m : Modulus k K) (v : Place k K)
    (Q : Ideal (integralClosure v.toValuationSubring (SeparableClosure K))) :
    normalizationDecompositionGroup v.toValuationSubring K (SeparableClosure K) Q →*
      localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m :=
  ((QuotientGroup.mk' (artinRaySubgroup m)).comp
    (localAbsoluteAbelianizationQuotientMap K)).comp
      (normalizationDecompositionInclusion v.toValuationSubring K (SeparableClosure K) Q)

/-- Each original decomposition representative is sent through the two
literal quotient maps without changing its underlying field automorphism. -/
theorem normalizationRayQuotientMap_apply (m : Modulus k K) (v : Place k K)
    (Q : Ideal (integralClosure v.toValuationSubring (SeparableClosure K)))
    (d : normalizationDecompositionGroup v.toValuationSubring K (SeparableClosure K) Q) :
    normalizationRayQuotientMap m v Q d =
      QuotientGroup.mk' (artinRaySubgroup m)
        (localAbsoluteAbelianizationQuotientMap K d.val) := rfl

end NativeMap

attribute [local instance] normalizationAmbientAlgebra normalizationAmbientTower

section Transport

variable {k₁ K₁ k₂ K₂ : Type*}
    [Field k₁] [Finite k₁] [Field K₁] [Algebra k₁ K₁]
    [Algebra (RatFunc k₁) K₁] [IsScalarTower k₁ (RatFunc k₁) K₁]
    [FunctionField k₁ K₁] [HasPrincipalDivisors k₁ K₁]
    [Field k₂] [Finite k₂] [Field K₂] [Algebra k₂ K₂]
    [Algebra (RatFunc k₂) K₂] [IsScalarTower k₂ (RatFunc k₂) K₂]
    [FunctionField k₂ K₂] [HasPrincipalDivisors k₂ K₂]

variable (m₁ : Modulus k₁ K₁) (v₁ : Place k₁ K₁)
    (Q₁ : Ideal (integralClosure v₁.toValuationSubring (SeparableClosure K₁)))
    (m₂ : Modulus k₂ K₂) (v₂ : Place k₂ K₂)
    (Q₂ : Ideal (integralClosure v₂.toValuationSubring (SeparableClosure K₂)))
    (γ : (localAbsoluteAbelianProfinite K₁ ⧸ artinRaySubgroup m₁) ≃*
      (localAbsoluteAbelianProfinite K₂ ⧸ artinRaySubgroup m₂))
    (hD : (normalizationRayQuotientMap m₁ v₁ Q₁).range.map γ.toMonoidHom =
      (normalizationRayQuotientMap m₂ v₂ Q₂).range)

include hD in
/-- The supplied correspondence of original decomposition images carries
each original representative to the quotient of an actual representative
in the corresponding original decomposition group. -/
theorem normalizationRayQuotientMap_exists_transport
    (d : normalizationDecompositionGroup v₁.toValuationSubring K₁
      (SeparableClosure K₁) Q₁) :
    ∃ d' : normalizationDecompositionGroup v₂.toValuationSubring K₂
        (SeparableClosure K₂) Q₂,
      QuotientGroup.mk' (artinRaySubgroup m₂)
          (localAbsoluteAbelianizationQuotientMap K₂ d'.val) =
        γ (QuotientGroup.mk' (artinRaySubgroup m₁)
          (localAbsoluteAbelianizationQuotientMap K₁ d.val)) := by
  have hmem : γ (normalizationRayQuotientMap m₁ v₁ Q₁ d) ∈
      (normalizationRayQuotientMap m₂ v₂ Q₂).range := by
    rw [← hD]
    exact ⟨normalizationRayQuotientMap m₁ v₁ Q₁ d, ⟨d, rfl⟩, rfl⟩
  obtain ⟨d', hd'⟩ := hmem
  refine ⟨d', ?_⟩
  simpa only [normalizationRayQuotientMap_apply] using hd'

include hD in
/-- Every target decomposition representative also comes from an original
source representative, at the same two literal quotient maps. -/
theorem normalizationRayQuotientMap_exists_source
    (d' : normalizationDecompositionGroup v₂.toValuationSubring K₂
      (SeparableClosure K₂) Q₂) :
    ∃ d : normalizationDecompositionGroup v₁.toValuationSubring K₁
        (SeparableClosure K₁) Q₁,
      γ (QuotientGroup.mk' (artinRaySubgroup m₁)
          (localAbsoluteAbelianizationQuotientMap K₁ d.val)) =
        QuotientGroup.mk' (artinRaySubgroup m₂)
          (localAbsoluteAbelianizationQuotientMap K₂ d'.val) := by
  have hmem : normalizationRayQuotientMap m₂ v₂ Q₂ d' ∈
      (normalizationRayQuotientMap m₁ v₁ Q₁).range.map γ.toMonoidHom := by
    rw [hD]
    exact ⟨d', rfl⟩
  obtain ⟨a, ⟨d, rfl⟩, hd⟩ := hmem
  refine ⟨d, ?_⟩
  change γ (normalizationRayQuotientMap m₁ v₁ Q₁ d) =
    normalizationRayQuotientMap m₂ v₂ Q₂ d' at hd
  exact hd

variable [Q₁.IsPrime] [Q₁.LiesOver (IsLocalRing.maximalIdeal v₁.toValuationSubring)]
    [Q₂.IsPrime] [Q₂.LiesOver (IsLocalRing.maximalIdeal v₂.toValuationSubring)]

include hD in
/-- Native decomposition-image preservation gives covariance of the
actual closed local reciprocity images. -/
theorem localRayClosure_map_of_nativeDecomposition :
    (localRayAbsoluteArtin m₁ v₁).range.topologicalClosure.map γ.toMonoidHom =
      (localRayAbsoluteArtin m₂ v₂).range.topologicalClosure := by
  rw [localRayAbsoluteArtin_closure_eq_decomposition m₁ v₁ Q₁,
    localRayAbsoluteArtin_closure_eq_decomposition m₂ v₂ Q₂]
  exact hD

include hD in
/-- The closed-local-image hypothesis of multiplicative reconstruction is
supplied by the original normalization decomposition correspondence. -/
theorem localRayClosure_mem_iff_of_nativeDecomposition
    (g : localAbsoluteAbelianProfinite K₁ ⧸ artinRaySubgroup m₁) :
    g ∈ (localRayAbsoluteArtin m₁ v₁).range.topologicalClosure ↔
      γ g ∈ (localRayAbsoluteArtin m₂ v₂).range.topologicalClosure := by
  have hmap := localRayClosure_map_of_nativeDecomposition m₁ v₁ Q₁ m₂ v₂ Q₂ γ hD
  constructor
  · intro hg
    rw [← hmap]
    exact ⟨g, hg, rfl⟩
  · intro hg
    rw [← hmap] at hg
    obtain ⟨a, ha, hag⟩ := hg
    exact (γ.injective hag) ▸ ha

end Transport

end FunctionField.RayClass

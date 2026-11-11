/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.DegreeOneAbsoluteGalois
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.DegreeOneArtinNaturality
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.NativeRayArtinTransfer
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayTower

/-!
# Native ray reciprocity under an actual degree-one coefficient map

The original absolute reciprocity square for a degree-one extension
preserves the original ray subgroup. Its quotient therefore acts on the
native ray groups. Equality of the pulled-back modulus with a specified
modulus is retained in the actual target, rather than replacing its field
or its reciprocal map. Original idele representatives prove the restricted
product square.
-/

@[expose] public section

universe u v w

noncomputable section

namespace FunctionField.RayClass

open AlgebraicCurve LocalClassFieldTheory

variable (k : Type u) (K : Type v) (F : Type w)
  [Field k] [Finite k] [Field K] [Field F]
  [Algebra k K] [Algebra k F] [Algebra K F] [IsScalarTower k K F]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
  [FiniteDimensional K F] [IsGalois K F]
  [HasPrincipalDivisors k K] [HasPrincipalDivisors k F]
  [Algebra K (SeparableClosure F)] [IsScalarTower K F (SeparableClosure F)]
  (hKF : Module.finrank K F = 1)
  (eΩ : SeparableClosure F ≃ₐ[K] SeparableClosure K)

local notation "δ" => ContinuousMulEquiv.symm (degreeOneAbsoluteAbelianEquiv K F hKF eΩ)

/-- In the forward coefficient direction the actual absolute Artin map
is carried by the inverse of the native restriction comparison. -/
theorem absoluteArtin_degreeOne_forward (c : IdeleClassGroup k K) :
    δ (absoluteArtin k K c) =
      absoluteArtin k F (IdeleClassGroup.baseChange (k := k) (K := K) (L := F) c) := by
  apply (degreeOneAbsoluteAbelianEquiv K F hKF eΩ).injective
  rw [ContinuousMulEquiv.apply_symm_apply]
  exact (absoluteArtin_baseChange_of_finrank_one k K F hKF eΩ c).symm

variable (m : Modulus k K) (n : Modulus k F)
  (hm : ∀ v, m v ≤ 1) (hn : rayModulusBaseChange F m = n)

include hm hn in
/-- Original degree-one covariance carries the actual reduced ray
subgroup into the actual subgroup for the specified target modulus. -/
theorem degreeOneAbsoluteAbelianEquiv_mem_artinRaySubgroup
    (a : localAbsoluteAbelianProfinite K) (ha : a ∈ artinRaySubgroup m) :
    δ a ∈ artinRaySubgroup n := by
  obtain ⟨c, hc, rfl⟩ := ha
  refine ⟨IdeleClassGroup.baseChange (k := k) (K := K) (L := F) c, ?_, ?_⟩
  · rw [← hn]
    exact baseChange_mem_reducedRayClassSubgroup m hm c hc
  · exact (absoluteArtin_degreeOne_forward k K F hKF eΩ c).symm

/-- The quotient of the original native Galois comparison, retaining the
specified pulled-back modulus as the actual codomain. -/
def degreeOneRayHom :
    (localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m) →ₜ*
      (localAbsoluteAbelianProfinite F ⧸ artinRaySubgroup n) := by
  let f := QuotientGroup.map (artinRaySubgroup m) (artinRaySubgroup n)
    (δ).toMonoidHom
    (degreeOneAbsoluteAbelianEquiv_mem_artinRaySubgroup
      k K F hKF eΩ m n hm hn)
  refine { toMonoidHom := f, continuous_toFun := ?_ }
  rw [← (QuotientGroup.isOpenQuotientMap_mk
    (N := artinRaySubgroup m)).continuous_comp_iff]
  exact QuotientGroup.continuous_mk.comp (δ).continuous_toFun

/-- Every original native abelian representative keeps its literal
degree-one Galois image in the quotient. -/
theorem degreeOneRayHom_mk (a : localAbsoluteAbelianProfinite K) :
    degreeOneRayHom k K F hKF eΩ m n hm hn
        (QuotientGroup.mk' (artinRaySubgroup m) a) =
      QuotientGroup.mk' (artinRaySubgroup n) (δ a) := rfl

/-- The same quotient on an original Galois representative is the
literal inverse closure conjugation of that representative. -/
theorem degreeOneRayHom_mk_mk (σ : Gal(SeparableClosure K/K)) :
    degreeOneRayHom k K F hKF eΩ m n hm hn
        (QuotientGroup.mk' (artinRaySubgroup m)
          (QuotientGroup.mk σ : localAbsoluteAbelianProfinite K)) =
      QuotientGroup.mk' (artinRaySubgroup n)
        (QuotientGroup.mk ((degreeOneAbsoluteGaloisEquiv K F hKF eΩ).symm σ) :
          localAbsoluteAbelianProfinite F) := rfl

/-- The native quotient and actual completion-induced restricted-product
map satisfy the original reciprocity square. -/
theorem restrictedProductAbsoluteArtin_degreeOne (a : RayRestrictedProduct m) :
    restrictedProductAbsoluteArtin n
        (rayModulusCongr hn (restrictedRayBaseChange (L := F) m hm a)) =
      degreeOneRayHom k K F hKF eΩ m n hm hn
        (restrictedProductAbsoluteArtin m a) := by
  obtain ⟨b, rfl⟩ := ideleToRayRestrictedProduct_surjective m a
  rw [restrictedRayBaseChange_idele, rayModulusCongr_idele,
    restrictedProductAbsoluteArtin_idele, restrictedProductAbsoluteArtin_idele,
    degreeOneRayHom_mk, ← IdeleClassGroup.baseChange_mk]
  exact congrArg (QuotientGroup.mk' (artinRaySubgroup n))
    (absoluteArtin_degreeOne_forward k K F hKF eΩ (IdeleClassGroup.mk b)).symm

end FunctionField.RayClass

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayProduct
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RayArtinSeparation
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve

/-!
# The principal kernel of actual restricted-product reciprocity

The original absolute Artin map, modulo the Artin image of the actual ray
congruence subgroup, has kernel precisely the diagonal function group in the
restricted product of local ray factors. For a nonzero modulus that diagonal
map is injective. The resulting kernel equivalence retains every normalized
valuation and the complete boundary group `1 + 𝔪_v`.
-/

@[expose] public section

universe u v

noncomputable section

namespace FunctionField.RayClass

open AlgebraicCurve LocalClassFieldTheory

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [HasPrincipalDivisors k K] [Finite k] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- Actual absolute reciprocity on the restricted product of local ray factors. -/
def restrictedProductAbsoluteArtin (m : Modulus k K) :
    RayRestrictedProduct m →* localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m :=
  (rayClassAbsoluteArtin m).comp (restrictedProductToRayClass m)

/-- On every idele this is its original absolute Artin image. -/
theorem restrictedProductAbsoluteArtin_idele (m : Modulus k K) (a : IdeleGroup k K) :
    restrictedProductAbsoluteArtin m (ideleToRayRestrictedProduct m a) =
      QuotientGroup.mk' (artinRaySubgroup m) (absoluteArtin k K (IdeleClassGroup.mk a)) := by
  have he : rayLocalRestrictedProductEquiv m (QuotientGroup.mk' (congruenceSubgroup m) a) =
      ideleToRayRestrictedProduct m a := rfl
  rw [← he]
  change rayClassAbsoluteArtin m (localToRayClass m ((rayLocalRestrictedProductEquiv m).symm
    (rayLocalRestrictedProductEquiv m (QuotientGroup.mk' (congruenceSubgroup m) a)))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The actual reciprocity kernel is exactly the original diagonal function group. -/
theorem restrictedProductAbsoluteArtin_ker (m : Modulus k K) :
    (restrictedProductAbsoluteArtin m).ker = (principalToRayRestrictedProduct m).range :=
  (MonoidHom.ker_comp_of_injective (restrictedProductToRayClass m)
    (rayClassAbsoluteArtin m) (rayClassAbsoluteArtin_injective m)).trans
      (restrictedProductToRayClass_ker m)

/-- The whole multiplicative function group is the principal kernel of the
actual reciprocity map, for every nonempty modulus. -/
def principalRestrictedArtinKernelEquiv (m : Modulus k K) (hm : m ≠ 0) :
    Kˣ ≃* (restrictedProductAbsoluteArtin m).ker := by
  have hcurve : IsCurveOver k K := FunctionField.isCurveOver k K
  have hres : ∀ v : Place k K, v.FiniteResidue :=
    fun v => ⟨IsCurveOver.finiteResidue v⟩
  exact (MonoidHom.ofInjective (principalToRayRestrictedProduct_injective m hm)).trans
    (MulEquiv.subgroupCongr (restrictedProductAbsoluteArtin_ker m).symm)

/-- The kernel equivalence is the actual diagonal map into the local restricted product. -/
theorem principalRestrictedArtinKernelEquiv_coe
    (m : Modulus k K) (hm : m ≠ 0) (x : Kˣ) :
    (principalRestrictedArtinKernelEquiv m hm x : RayRestrictedProduct m) =
      principalToRayRestrictedProduct m x := rfl

/-- Each coordinate is the original completion embedding, modulo the prescribed units. -/
theorem principalRestrictedArtinKernelEquiv_apply
    (m : Modulus k K) (hm : m ≠ 0) (x : Kˣ) (v : Place k K) :
    (principalRestrictedArtinKernelEquiv m hm x : RayRestrictedProduct m) v =
      QuotientGroup.mk' (localHigherUnitGroup v (m v))
        (Units.map (algebraMap K v.adicCompletion) x) := rfl

/-- Every normalized integer valuation on the actual local restricted product. -/
def restrictedRayOrder (m : Modulus k K) (v : Place k K) :
    RayRestrictedProduct m →* Multiplicative ℤ :=
  (rayLocalOrder m v).comp (rayLocalRestrictedProductEquiv m).symm.toMonoidHom

/-- Actual reciprocity reconstructs all original normalized valuations on its principal kernel. -/
theorem restrictedRayOrder_principalRestrictedArtinKernelEquiv
    (m : Modulus k K) (hm : m ≠ 0) (x : Kˣ) (v : Place k K) :
    (restrictedRayOrder m v (principalRestrictedArtinKernelEquiv m hm x)).toAdd =
      v.ord (x : K) := by
  rw [principalRestrictedArtinKernelEquiv_coe]
  change (rayLocalOrder m v ((rayLocalRestrictedProductEquiv m).symm
    (rayLocalRestrictedProductEquiv m (principalToRayLocal m x)))).toAdd = _
  rw [MulEquiv.symm_apply_apply]
  exact IdeleGroup.localOrder_algebraMap v x

/-- At a reduced boundary place, triviality of the kernel coordinate is
membership in the full actual group `1 + 𝔪_v`. -/
theorem principalRestrictedArtinKernelEquiv_boundary
    (m : Modulus k K) (hm : m ≠ 0) (x : Kˣ) (v : Place k K) (hv : m v = 1) :
    (principalRestrictedArtinKernelEquiv m hm x : RayRestrictedProduct m) v = 1 ↔
      Units.map (algebraMap K v.adicCompletion) x ∈ localHigherUnitGroup v 1 := by
  rw [principalRestrictedArtinKernelEquiv_apply]
  have h := QuotientGroup.eq_one_iff (N := localHigherUnitGroup v (m v))
    (Units.map (algebraMap K v.adicCompletion) x)
  exact h.trans (by rw [hv])

end FunctionField.RayClass

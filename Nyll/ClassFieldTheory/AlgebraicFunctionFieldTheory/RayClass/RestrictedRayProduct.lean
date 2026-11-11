/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.PrincipalRayKernel

/-!
# The restricted product of actual local ray factors

The quotient of all-place ideles by the actual local congruence groups is
canonically the restricted product of the local quotients. Outside the
modulus support these are valuation quotients; at a reduced boundary they
retain the full quotient by `1 + 𝔪_v`.

All coordinate maps are the original completion maps. The principal kernel
is therefore realized inside this actual restricted product.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve Filter
open scoped RestrictedProduct

namespace FunctionField.RayClass

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Restricted product of the actual local ray factors relative to their
identity subgroups. -/
def RayRestrictedProduct (m : Modulus k K) :=
  Πʳ v : Place k K, [RayLocalFactor m v, (⊥ : Subgroup (RayLocalFactor m v))]

/-- The canonical group structure is supplied once by the actual restricted product. -/
instance rayRestrictedProductCommGroup (m : Modulus k K) : CommGroup (RayRestrictedProduct m) :=
  inferInstanceAs (CommGroup
    (Πʳ v : Place k K, [RayLocalFactor m v, (⊥ : Subgroup (RayLocalFactor m v))]))

/-- Local coordinates of an actual restricted family. -/
instance rayRestrictedProductCoeFun (m : Modulus k K) :
    CoeFun (RayRestrictedProduct m) (fun _ => ∀ v : Place k K, RayLocalFactor m v) :=
  ⟨fun a => a.1⟩

/-- The original local quotient maps assemble on all-place ideles. -/
def ideleToRayRestrictedProduct (m : Modulus k K) :
    IdeleGroup k K →* RayRestrictedProduct m where
  toFun a := ⟨fun v => QuotientGroup.mk' (localHigherUnitGroup v (m v)) (a v), by
    have hm : ∀ᶠ v in cofinite, m v = 0 :=
      Filter.eventually_cofinite.mpr m.hasFiniteSupport
    filter_upwards [a.2, hm] with v hv hm
    change QuotientGroup.mk' (localHigherUnitGroup v (m v)) (a v) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [hm, localHigherUnitGroup_zero]
    exact hv⟩
  map_one' := by
    apply RestrictedProduct.ext
    intro v
    exact map_one (QuotientGroup.mk' (localHigherUnitGroup v (m v)))
  map_mul' a b := by
    apply RestrictedProduct.ext
    intro v
    exact map_mul (QuotientGroup.mk' (localHigherUnitGroup v (m v))) (a v) (b v)

/-- Every restricted family of local classes has an actual idele representative. -/
theorem ideleToRayRestrictedProduct_surjective (m : Modulus k K) :
    Function.Surjective (ideleToRayRestrictedProduct m) := by
  intro q
  choose a ha using fun v => QuotientGroup.mk'_surjective (localHigherUnitGroup v (m v)) (q v)
  let x : IdeleGroup k K := ⟨a, q.2.mono fun v hv =>
    localHigherUnitGroup_le_localUnits v (m v)
      ((QuotientGroup.eq_one_iff _).mp ((ha v).trans hv))⟩
  exact ⟨x, RestrictedProduct.ext _ _ ha⟩

/-- The actual congruence subgroup is exactly the kernel of all local quotients. -/
theorem ideleToRayRestrictedProduct_ker (m : Modulus k K) :
    (ideleToRayRestrictedProduct m).ker = congruenceSubgroup m := by
  apply Subgroup.ext
  intro a
  constructor
  · intro ha v
    have hv := congrArg (fun q : RayRestrictedProduct m => q v) ha
    exact (QuotientGroup.eq_one_iff _).mp hv
  · intro ha
    apply RestrictedProduct.ext
    intro v
    exact (QuotientGroup.eq_one_iff _).mpr (ha v)

/-- The idele quotient is canonically the restricted product of the original
local unit quotients. -/
def rayLocalRestrictedProductEquiv (m : Modulus k K) :
    RayLocalQuotient m ≃* RayRestrictedProduct m :=
  QuotientGroup.liftEquiv (congruenceSubgroup m)
    (ideleToRayRestrictedProduct_surjective m) (ideleToRayRestrictedProduct_ker m).symm

/-- This equivalence is the original local quotient on every idele component. -/
theorem rayLocalRestrictedProductEquiv_mk_apply
    (m : Modulus k K) (a : IdeleGroup k K) (v : Place k K) :
    rayLocalRestrictedProductEquiv m (QuotientGroup.mk' (congruenceSubgroup m) a) v =
      QuotientGroup.mk' (localHigherUnitGroup v (m v)) (a v) := rfl

variable [HasPrincipalDivisors k K]

/-- The ray-class map on the actual restricted product. -/
def restrictedProductToRayClass (m : Modulus k K) :
    RayRestrictedProduct m →* RayClassGroup m :=
  (localToRayClass m).comp (rayLocalRestrictedProductEquiv m).symm.toMonoidHom

/-- The original diagonal rational-function map into the actual local product. -/
def principalToRayRestrictedProduct (m : Modulus k K) : Kˣ →* RayRestrictedProduct m :=
  (rayLocalRestrictedProductEquiv m).toMonoidHom.comp (principalToRayLocal m)

/-- The restricted-product ray-class kernel consists precisely of the
original diagonal rational functions. -/
theorem restrictedProductToRayClass_ker (m : Modulus k K) :
    (restrictedProductToRayClass m).ker = (principalToRayRestrictedProduct m).range := by
  apply Subgroup.ext
  intro q
  change localToRayClass m ((rayLocalRestrictedProductEquiv m).symm q) = 1 ↔ _
  rw [← MonoidHom.mem_ker, localToRayClass_ker]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact (congrArg (rayLocalRestrictedProductEquiv m) hx).trans
      ((rayLocalRestrictedProductEquiv m).apply_symm_apply q)
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact ((rayLocalRestrictedProductEquiv m).symm_apply_apply (principalToRayLocal m x)).symm.trans
      (congrArg (rayLocalRestrictedProductEquiv m).symm hx)

variable [∀ v : Place k K, v.FiniteResidue]

/-- The original rational-function group embeds in the actual restricted
product for every nonempty modulus. -/
theorem principalToRayRestrictedProduct_injective (m : Modulus k K) (hm : m ≠ 0) :
    Function.Injective (principalToRayRestrictedProduct m) :=
  (rayLocalRestrictedProductEquiv m).injective.comp (principalToRayLocal_injective m hm)

/-- The principal kernel in the actual restricted product is the entire
multiplicative group of the original function field. -/
def principalRestrictedRayKernelEquiv (m : Modulus k K) (hm : m ≠ 0) :
    Kˣ ≃* (restrictedProductToRayClass m).ker :=
  (MonoidHom.ofInjective (principalToRayRestrictedProduct_injective m hm)).trans
    (MulEquiv.subgroupCongr (restrictedProductToRayClass_ker m).symm)

/-- Each kernel coordinate is the original function in its actual completion. -/
theorem principalRestrictedRayKernelEquiv_apply
    (m : Modulus k K) (hm : m ≠ 0) (x : Kˣ) (v : Place k K) :
    (principalRestrictedRayKernelEquiv m hm x : RayRestrictedProduct m) v =
      QuotientGroup.mk' (localHigherUnitGroup v (m v))
        (Units.map (algebraMap K v.adicCompletion) x) := rfl

end FunctionField.RayClass

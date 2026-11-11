/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayReconstruction
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayTransport
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RayPrincipalUnitValues
public import Mathlib.Algebra.GroupWithZero.WithZero

/-!
# Multiplication reconstructed from the original ray-Artin quotients

An equivalence of the original ray-Artin quotients, together with its
correspondence of closed local images and its arithmetic degree identity,
determines the actual local multiplicative maps. Their coordinatewise map
on the original restricted products commutes with global reciprocity: this
is proved from the original one-place inclusions and finite support.

The resulting map on the original Artin kernels therefore reconstructs a
multiplicative equivalence of the actual function units. It preserves every
normalized order and the full residue-value-one predicate at each reduced
boundary component. Neither the global reciprocity square nor the kernel
correspondence nor a function-field equivalence is an input.

The comparison of these original ray-Artin quotients with the input affine
fundamental groups is separate; no such comparison is asserted here.
-/

@[expose] public section

universe u v u₁ v₁ u₂ v₂

noncomputable section

open AlgebraicCurve LocalClassFieldTheory

namespace FunctionField.RayClass

section CoordinateOrder

variable {k : Type u} {K : Type v} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K]

omit [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] [HasPrincipalDivisors k K] in
/-- The order previously defined through the idele quotient is exactly the
order of the actual local coordinate of the restricted ray family. -/
theorem restrictedRayOrder_eq_localRayFactorOrder
    (m : Modulus k K) (v : Place k K) (a : RayRestrictedProduct m) :
    restrictedRayOrder m v a = localRayFactorOrder m v (a v) := by
  obtain ⟨b, rfl⟩ := ideleToRayRestrictedProduct_surjective m a
  have hb : ideleToRayRestrictedProduct m b =
      rayLocalRestrictedProductEquiv m (QuotientGroup.mk' (congruenceSubgroup m) b) := rfl
  rw [hb]
  change rayLocalOrder m v ((rayLocalRestrictedProductEquiv m).symm
      (rayLocalRestrictedProductEquiv m (QuotientGroup.mk' (congruenceSubgroup m) b))) = _
  rw [MulEquiv.symm_apply_apply, rayLocalRestrictedProductEquiv_mk_apply]
  rfl

end CoordinateOrder

section Reconstruction

variable {k₁ : Type u₁} {K₁ : Type v₁} {k₂ : Type u₂} {K₂ : Type v₂}
    [Field k₁] [Finite k₁] [Field K₁] [Algebra k₁ K₁]
    [Algebra (RatFunc k₁) K₁] [IsScalarTower k₁ (RatFunc k₁) K₁]
    [FunctionField k₁ K₁] [HasPrincipalDivisors k₁ K₁]
    [Field k₂] [Finite k₂] [Field K₂] [Algebra k₂ K₂]
    [Algebra (RatFunc k₂) K₂] [IsScalarTower k₂ (RatFunc k₂) K₂]
    [FunctionField k₂ K₂] [HasPrincipalDivisors k₂ K₂]

variable (m₁ : Modulus k₁ K₁) (m₂ : Modulus k₂ K₂)
    (e : Place k₁ K₁ ≃ Place k₂ K₂)
    (γ : (localAbsoluteAbelianProfinite K₁ ⧸ artinRaySubgroup m₁) ≃*
      (localAbsoluteAbelianProfinite K₂ ⧸ artinRaySubgroup m₂))
    (hclosure : ∀ v g,
      g ∈ (localRayAbsoluteArtin m₁ v).range.topologicalClosure ↔
        γ g ∈ (localRayAbsoluteArtin m₂ (e v)).range.topologicalClosure)
    (hdegree : ∀ g, rayAbelianDegree m₂ (γ g) = rayAbelianDegree m₁ g)
    (hboundary₁ : ∀ v : Place k₁ K₁, ∃ w : Place k₁ K₁, w ≠ v ∧ m₁ w ≠ 0)
    (hboundary₂ : ∀ v : Place k₂ K₂, ∃ w : Place k₂ K₂, w ≠ v ∧ m₂ w ≠ 0)

local notation "φ" => fun v => localRayEquivOfClosure m₁ v m₂ (e v)
  γ (hclosure v) hdegree (hboundary₁ v) (hboundary₂ (e v))

/-- The actual restricted-product map assembled from the locally reconstructed
Artin maps, with its finite-support condition and inverse. -/
def reconstructedRestrictedRayEquiv : RayRestrictedProduct m₁ ≃* RayRestrictedProduct m₂ :=
  restrictedRayEquiv e φ

/-- The reconstructed global map retains the original local coordinates. -/
theorem reconstructedRestrictedRayEquiv_apply
    (a : RayRestrictedProduct m₁) (v : Place k₁ K₁) :
    reconstructedRestrictedRayEquiv m₁ m₂ e γ hclosure hdegree hboundary₁ hboundary₂ a (e v) =
      φ v (a v) :=
  restrictedRayEquiv_apply e φ a v

/-- Original local Artin commutation implies original global Artin commutation,
by the proved finite-support decomposition of each restricted ray family. -/
theorem reconstructedRestrictedRayEquiv_artin (a : RayRestrictedProduct m₁) :
    restrictedProductAbsoluteArtin m₂
        (reconstructedRestrictedRayEquiv m₁ m₂ e γ hclosure hdegree hboundary₁ hboundary₂ a) =
      γ (restrictedProductAbsoluteArtin m₁ a) := by
  have h : (restrictedProductAbsoluteArtin m₂).comp
      (reconstructedRestrictedRayEquiv m₁ m₂ e γ hclosure hdegree
        hboundary₁ hboundary₂).toMonoidHom =
      γ.toMonoidHom.comp (restrictedProductAbsoluteArtin m₁) := by
    apply restrictedRay_hom_ext m₁
    intro v x
    change restrictedProductAbsoluteArtin m₂
      (restrictedRayEquiv e φ (localRayToRestrictedProduct m₁ v x)) =
        γ (restrictedProductAbsoluteArtin m₁ (localRayToRestrictedProduct m₁ v x))
    rw [restrictedRayEquiv_local]
    exact localRayAbsoluteArtin_map m₁ v m₂ (e v) γ
      (hclosure v) hdegree (hboundary₁ v) (hboundary₂ (e v)) x
  exact DFunLike.congr_fun h a

/-- The reconstructed global map preserves every original normalized order. -/
theorem reconstructedRestrictedRayEquiv_order
    (a : RayRestrictedProduct m₁) (v : Place k₁ K₁) :
    restrictedRayOrder m₂ (e v)
        (reconstructedRestrictedRayEquiv m₁ m₂ e γ hclosure hdegree hboundary₁ hboundary₂ a) =
      restrictedRayOrder m₁ v a := by
  rw [restrictedRayOrder_eq_localRayFactorOrder,
    reconstructedRestrictedRayEquiv_apply, restrictedRayOrder_eq_localRayFactorOrder]
  exact localRayFactorOrder_map m₁ v m₂ (e v) γ
    (hclosure v) hdegree (hboundary₁ v) (hboundary₂ (e v)) (a v)

/-- The kernel of the original reciprocity map is preserved as a consequence
of the constructed global square, in both directions. -/
def reconstructedRayKernelEquiv :
    (restrictedProductAbsoluteArtin m₁).ker ≃* (restrictedProductAbsoluteArtin m₂).ker where
  toFun a := ⟨reconstructedRestrictedRayEquiv m₁ m₂ e γ hclosure hdegree
    hboundary₁ hboundary₂ a.val, by
      change restrictedProductAbsoluteArtin m₂ _ = 1
      rw [reconstructedRestrictedRayEquiv_artin]
      exact (congrArg γ a.property).trans (map_one γ)⟩
  invFun b := ⟨(reconstructedRestrictedRayEquiv m₁ m₂ e γ hclosure hdegree
    hboundary₁ hboundary₂).symm b.val, by
      change restrictedProductAbsoluteArtin m₁ _ = 1
      apply γ.injective
      rw [map_one]
      rw [← reconstructedRestrictedRayEquiv_artin m₁ m₂ e γ hclosure hdegree
        hboundary₁ hboundary₂,
        MulEquiv.apply_symm_apply]
      exact b.property⟩
  left_inv a := Subtype.ext
    ((reconstructedRestrictedRayEquiv m₁ m₂ e γ hclosure hdegree
      hboundary₁ hboundary₂).symm_apply_apply a.val)
  right_inv b := Subtype.ext
    ((reconstructedRestrictedRayEquiv m₁ m₂ e γ hclosure hdegree
      hboundary₁ hboundary₂).apply_symm_apply b.val)
  map_mul' a b := Subtype.ext
    (map_mul (reconstructedRestrictedRayEquiv m₁ m₂ e γ hclosure hdegree
      hboundary₁ hboundary₂) a.val b.val)

/-- Kernel transport is literally the constructed map on original ray families. -/
theorem reconstructedRayKernelEquiv_coe
    (a : (restrictedProductAbsoluteArtin m₁).ker) :
    (reconstructedRayKernelEquiv m₁ m₂ e γ hclosure hdegree hboundary₁ hboundary₂ a :
      RayRestrictedProduct m₂) =
      reconstructedRestrictedRayEquiv m₁ m₂ e γ hclosure hdegree hboundary₁ hboundary₂ a.val :=
  rfl

variable (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0)

/-- Multiplication on the actual rational-function units, reconstructed from
the original ray quotient comparison through its original principal kernel. -/
def reconstructedRayFunctionUnits : K₁ˣ ≃* K₂ˣ :=
  (principalRestrictedArtinKernelEquiv m₁ hm₁).trans
    ((reconstructedRayKernelEquiv m₁ m₂ e γ hclosure hdegree
      hboundary₁ hboundary₂).trans (principalRestrictedArtinKernelEquiv m₂ hm₂).symm)

/-- The recovered rational function has exactly the transported original
principal idele, not merely the same divisor or a prime-primary image. -/
theorem reconstructedRayFunctionUnits_principal (x : K₁ˣ) :
    (principalRestrictedArtinKernelEquiv m₂ hm₂
      (reconstructedRayFunctionUnits m₁ m₂ e γ hclosure hdegree
        hboundary₁ hboundary₂ hm₁ hm₂ x) : RayRestrictedProduct m₂) =
      reconstructedRestrictedRayEquiv m₁ m₂ e γ hclosure hdegree
        hboundary₁ hboundary₂ (principalRestrictedArtinKernelEquiv m₁ hm₁ x) := by
  exact congrArg Subtype.val
    ((principalRestrictedArtinKernelEquiv m₂ hm₂).apply_symm_apply
      (reconstructedRayKernelEquiv m₁ m₂ e γ hclosure hdegree
        hboundary₁ hboundary₂ (principalRestrictedArtinKernelEquiv m₁ hm₁ x)))

/-- The original completion of the reconstructed function is the locally
reconstructed image of its original completion, at every matched place. -/
theorem reconstructedRayFunctionUnits_local (x : K₁ˣ) (v : Place k₁ K₁) :
    QuotientGroup.mk' (localHigherUnitGroup (e v) (m₂ (e v)))
        (Units.map (algebraMap K₂ (e v).adicCompletion)
          (reconstructedRayFunctionUnits m₁ m₂ e γ hclosure hdegree
            hboundary₁ hboundary₂ hm₁ hm₂ x)) =
      φ v (QuotientGroup.mk' (localHigherUnitGroup v (m₁ v))
        (Units.map (algebraMap K₁ v.adicCompletion) x)) := by
  have h := congrArg (fun a : RayRestrictedProduct m₂ => a (e v))
    (reconstructedRayFunctionUnits_principal m₁ m₂ e γ hclosure hdegree
      hboundary₁ hboundary₂ hm₁ hm₂ x)
  rw [principalRestrictedArtinKernelEquiv_apply,
    reconstructedRestrictedRayEquiv_apply, principalRestrictedArtinKernelEquiv_apply] at h
  exact h

/-- Original local reciprocity determines the recovered function uniquely,
including its constant factor. This also removes choices of representatives
or local inverses from any construction with the same original symbols. -/
theorem reconstructedRayFunctionUnits_unique
    (η : K₁ˣ →* K₂ˣ)
    (hη : ∀ (x : K₁ˣ) (v : Place k₁ K₁),
      localRayAbsoluteArtin m₂ (e v)
          (QuotientGroup.mk' (localHigherUnitGroup (e v) (m₂ (e v)))
            (Units.map (algebraMap K₂ (e v).adicCompletion) (η x))) =
        γ (localRayAbsoluteArtin m₁ v
          (QuotientGroup.mk' (localHigherUnitGroup v (m₁ v))
            (Units.map (algebraMap K₁ v.adicCompletion) x)))) :
    η = (reconstructedRayFunctionUnits m₁ m₂ e γ hclosure hdegree
      hboundary₁ hboundary₂ hm₁ hm₂).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  apply (principalRestrictedArtinKernelEquiv m₂ hm₂).injective
  apply Subtype.ext
  apply Subtype.ext
  funext w
  obtain ⟨v, rfl⟩ := e.surjective w
  change QuotientGroup.mk' (localHigherUnitGroup (e v) (m₂ (e v)))
      (Units.map (algebraMap K₂ (e v).adicCompletion) (η x)) =
    QuotientGroup.mk' (localHigherUnitGroup (e v) (m₂ (e v)))
      (Units.map (algebraMap K₂ (e v).adicCompletion)
        (reconstructedRayFunctionUnits m₁ m₂ e γ hclosure hdegree
          hboundary₁ hboundary₂ hm₁ hm₂ x))
  apply localRayAbsoluteArtin_injective m₂ (e v) (hboundary₂ (e v))
  rw [reconstructedRayFunctionUnits_local, localRayAbsoluteArtin_map]
  exact hη x v

/-- All original function-field orders are preserved by the reconstructed
multiplication, with their exact integer normalization. -/
theorem reconstructedRayFunctionUnits_order (x : K₁ˣ) (v : Place k₁ K₁) :
    (e v).ord (reconstructedRayFunctionUnits m₁ m₂ e γ hclosure hdegree
        hboundary₁ hboundary₂ hm₁ hm₂ x : K₂) = v.ord (x : K₁) := by
  rw [← restrictedRayOrder_principalRestrictedArtinKernelEquiv m₂ hm₂,
    reconstructedRayFunctionUnits_principal, reconstructedRestrictedRayEquiv_order,
    restrictedRayOrder_principalRestrictedArtinKernelEquiv]

/-- At every matched reduced boundary point, the reconstructed function has
residue value one exactly when the original function does. -/
theorem reconstructedRayFunctionUnits_boundary
    (x : K₁ˣ) (v : Place k₁ K₁) (hv₁ : m₁ v = 1) (hv₂ : m₂ (e v) = 1) :
    (e v).HasValue (reconstructedRayFunctionUnits m₁ m₂ e γ hclosure hdegree
        hboundary₁ hboundary₂ hm₁ hm₂ x : K₂) 1 ↔ v.HasValue (x : K₁) 1 := by
  have h₁ := (principalRestrictedArtinKernelEquiv_boundary m₁ hm₁ x v hv₁).trans
    (completion_mem_localHigherUnitGroup_one_iff_hasValue v x)
  have h₂ := (principalRestrictedArtinKernelEquiv_boundary m₂ hm₂
      (reconstructedRayFunctionUnits m₁ m₂ e γ hclosure hdegree
        hboundary₁ hboundary₂ hm₁ hm₂ x) (e v) hv₂).trans
    (completion_mem_localHigherUnitGroup_one_iff_hasValue (e v)
      (reconstructedRayFunctionUnits m₁ m₂ e γ hclosure hdegree
        hboundary₁ hboundary₂ hm₁ hm₂ x))
  rw [← h₂, reconstructedRayFunctionUnits_principal]
  exact (restrictedRayEquiv_apply_eq_one_iff e φ
    (principalRestrictedArtinKernelEquiv m₁ hm₁ x) v).trans h₁

/-- Adjoining zero to the reconstructed unit map gives a multiplicative
equivalence of the actual fields, before any assertion of additivity. -/
def reconstructedRayFunction : K₁ ≃* K₂ := by
  classical
  exact WithZero.withZeroUnitsEquiv.symm.trans
    ((MulEquiv.withZero (reconstructedRayFunctionUnits m₁ m₂ e γ hclosure hdegree
      hboundary₁ hboundary₂ hm₁ hm₂)).trans WithZero.withZeroUnitsEquiv)

/-- On every original nonzero function the extension is the same recovered unit. -/
theorem reconstructedRayFunction_apply_units (x : K₁ˣ) :
    reconstructedRayFunction m₁ m₂ e γ hclosure hdegree
        hboundary₁ hboundary₂ hm₁ hm₂ (x : K₁) =
      (reconstructedRayFunctionUnits m₁ m₂ e γ hclosure hdegree
        hboundary₁ hboundary₂ hm₁ hm₂ x : K₂) := by
  classical
  change WithZero.withZeroUnitsEquiv
    (MulEquiv.withZero (reconstructedRayFunctionUnits m₁ m₂ e γ hclosure hdegree
      hboundary₁ hboundary₂ hm₁ hm₂)
      (WithZero.withZeroUnitsEquiv.symm (x : K₁))) = _
  rw [WithZero.withZeroUnitsEquiv_symm_apply_coe]
  rfl

/-- The multiplicative field map preserves all original orders, including the
specified convention for the order of zero. -/
theorem reconstructedRayFunction_order (x : K₁) (v : Place k₁ K₁) :
    (e v).ord (reconstructedRayFunction m₁ m₂ e γ hclosure hdegree
        hboundary₁ hboundary₂ hm₁ hm₂ x) = v.ord x := by
  rcases GroupWithZero.eq_zero_or_unit x with rfl | ⟨u, rfl⟩
  · rw [map_zero, Place.ord_zero, Place.ord_zero]
  · rw [reconstructedRayFunction_apply_units]
    exact reconstructedRayFunctionUnits_order m₁ m₂ e γ hclosure hdegree
      hboundary₁ hboundary₂ hm₁ hm₂ u v

/-- The full boundary predicate is preserved on the entire original field,
so its later use in additive reconstruction does not need a nonzero side condition. -/
theorem reconstructedRayFunction_boundary
    (x : K₁) (v : Place k₁ K₁) (hv₁ : m₁ v = 1) (hv₂ : m₂ (e v) = 1) :
    (e v).HasValue (reconstructedRayFunction m₁ m₂ e γ hclosure hdegree
        hboundary₁ hboundary₂ hm₁ hm₂ x) 1 ↔ v.HasValue x 1 := by
  rcases GroupWithZero.eq_zero_or_unit x with rfl | ⟨u, rfl⟩
  · rw [map_zero]
    exact ⟨fun h => False.elim (h.ne_zero one_ne_zero rfl),
      fun h => False.elim (h.ne_zero one_ne_zero rfl)⟩
  · rw [reconstructedRayFunction_apply_units]
    exact reconstructedRayFunctionUnits_boundary m₁ m₂ e γ hclosure hdegree
      hboundary₁ hboundary₂ hm₁ hm₂ u v hv₁ hv₂

end Reconstruction

end FunctionField.RayClass

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.GroupTheory.DirectLimitCofinalTail
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricArtinBoundaryStages
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricArtinKernel
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricArtinKernelLocalization
public import Mathlib.Algebra.GroupWithZero.WithZero

/-!
# Geometric multiplication from a cofinal tail of native Artin kernels

Only sufficiently large finite constant stages need local Artin embeddings.
Their original compatible kernel maps determine multiplication on the
entire original geometric compositum. Earlier stages are moved by the
native transition maps; no boundary point is assumed split over the
original finite field. Every good-stage function, order, and boundary
principal unit retains its original value.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve

namespace FunctionField.RayClass

attribute [local instance]
  stageRatFuncAlgebra stageRatFuncTower stageFunctionField stagePrincipalDivisors
  geometricLocalizationConstants geometricLocalizationConstantTower

variable (k₁ K₁ Ω₁ k₂ K₂ Ω₂ : Type*)
    [Field k₁] [Finite k₁] [Field K₁] [Field Ω₁]
    [Algebra k₁ K₁] [Algebra (RatFunc k₁) K₁]
    [IsScalarTower k₁ (RatFunc k₁) K₁] [FunctionField k₁ K₁]
    [Algebra K₁ Ω₁] [IsSepClosed Ω₁] [Algebra k₁ Ω₁] [IsScalarTower k₁ K₁ Ω₁]
    [Field k₂] [Finite k₂] [Field K₂] [Field Ω₂]
    [Algebra k₂ K₂] [Algebra (RatFunc k₂) K₂]
    [IsScalarTower k₂ (RatFunc k₂) K₂] [FunctionField k₂ K₂]
    [Algebra K₂ Ω₂] [IsSepClosed Ω₂] [Algebra k₂ Ω₂] [IsScalarTower k₂ K₂ Ω₂]
    (m₁ : Modulus k₁ K₁) (m₂ : Modulus k₂ K₂)
    (hm₁ : ∀ v, m₁ v ≤ 1) (hm₂ : ∀ v, m₂ v ≤ 1)
    (hz₁ : m₁ ≠ 0) (hz₂ : m₂ ≠ 0)

local notation "I₁" => GeometricArtinIndex k₁ K₁ Ω₁
local notation "q" => geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂
local notation "A₁" => GeometricArtinStageKernel k₁ K₁ Ω₁ m₁
local notation "t₁" => geometricArtinTransition k₁ K₁ Ω₁ m₁ hm₁
local notation "t₂" => geometricArtinTransition k₂ K₂ Ω₂ m₂ hm₂
local notation "L₁" => GeometricArtinKernel k₁ K₁ Ω₁ m₁ hm₁ hz₁
local notation "G₁" => geometricConstantExtension k₁ K₁ Ω₁
local notation "G₂" => geometricConstantExtension k₂ K₂ Ω₂
local notation "e₁" => geometricArtinKernelEquiv k₁ K₁ Ω₁ m₁ hm₁ hz₁
local notation "e₂" => geometricArtinKernelEquiv k₂ K₂ Ω₂ m₂ hm₂ hz₂
local notation "u₂" => geometricArtinStageToUnits k₂ K₂ Ω₂ m₂ hz₂

variable (i₀ : GeometricArtinIndex k₁ K₁ Ω₁)
    (η : ∀ i : GeometricArtinIndex k₁ K₁ Ω₁, i₀ ≤ i →
      GeometricArtinStageKernel k₁ K₁ Ω₁ m₁ i ≃*
        GeometricArtinStageKernel k₂ K₂ Ω₂ m₂
          (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ i))
    (hη : ∀ (i j : GeometricArtinIndex k₁ K₁ Ω₁) (hi : i₀ ≤ i) (hj : i₀ ≤ j)
      (hij : i ≤ j) (a : GeometricArtinStageKernel k₁ K₁ Ω₁ m₁ i),
      η j hj (geometricArtinTransition k₁ K₁ Ω₁ m₁ hm₁ i j hij a) =
        geometricArtinTransition k₂ K₂ Ω₂ m₂ hm₂
          (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ i)
          (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ j)
          ((geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂).monotone hij) (η i hi a))

/-- Evaluate a transported Artin kernel from the cofinal tail in the target geometric units. -/
def cofinalStageToUnits (i : I₁) (hi : i₀ ≤ i) : A₁ i →* G₂ˣ :=
  (u₂ (q i)).comp (η i hi).toMonoidHom

include hη in
theorem cofinalStageToUnits_transition
    (i j : I₁) (hi : i₀ ≤ i) (hj : i₀ ≤ j) (hij : i ≤ j) (a : A₁ i) :
    cofinalStageToUnits k₁ K₁ Ω₁ k₂ K₂ Ω₂ m₁ m₂ hz₂ i₀ η i hi a =
      cofinalStageToUnits k₁ K₁ Ω₁ k₂ K₂ Ω₂ m₁ m₂ hz₂ i₀ η j hj
        (t₁ i j hij a) := by
  change u₂ (q i) (η i hi a) = u₂ (q j) (η j hj (t₁ i j hij a))
  rw [hη]
  exact (geometricArtinStageToUnits_transition k₂ K₂ Ω₂ m₂ hm₂ hz₂
    (q i) (q j) ((q).monotone hij) (η i hi a)).symm

/-- The native direct limit is evaluated using only its actual cofinal
tail maps, through the original transition from each earlier stage. -/
def cofinalGeometricArtinTransportToUnits : L₁ →* G₂ˣ := by
  let _ := geometricArtinDirectedSystem k₁ K₁ Ω₁ m₁ hm₁ hz₁
  exact DirectLimit.tailLift t₁ i₀
    (cofinalStageToUnits k₁ K₁ Ω₁ k₂ K₂ Ω₂ m₁ m₂ hz₂ i₀ η)
    (cofinalStageToUnits_transition k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₂ i₀ η hη)

/-- Every native representative in the cofinal tail keeps precisely its
prescribed finite-stage kernel value. -/
theorem cofinalGeometricArtinTransportToUnits_mk
    (i : I₁) (hi : i₀ ≤ i) (a : A₁ i) :
    cofinalGeometricArtinTransportToUnits k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ i₀ η hη ⟦⟨i, a⟩⟧ = u₂ (q i) (η i hi a) := by
  let _ := geometricArtinDirectedSystem k₁ K₁ Ω₁ m₁ hm₁ hz₁
  exact DirectLimit.tailLift_mk t₁ i₀
    (cofinalStageToUnits k₁ K₁ Ω₁ k₂ K₂ Ω₂ m₁ m₂ hz₂ i₀ η)
    (cofinalStageToUnits_transition k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₂ i₀ η hη) i hi a

/-- Injectivity uses only the original injective function inclusions and
the prescribed equivalences on the tail. -/
theorem cofinalGeometricArtinTransportToUnits_injective :
    Function.Injective (cofinalGeometricArtinTransportToUnits
      k₁ K₁ Ω₁ k₂ K₂ Ω₂ m₁ m₂ hm₁ hm₂ hz₁ hz₂ i₀ η hη) := by
  let _ := geometricArtinDirectedSystem k₁ K₁ Ω₁ m₁ hm₁ hz₁
  apply DirectLimit.tailLift_injective t₁ i₀
    (cofinalStageToUnits k₁ K₁ Ω₁ k₂ K₂ Ω₂ m₁ m₂ hz₂ i₀ η)
    (cofinalStageToUnits_transition k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₂ i₀ η hη)
  · intro i j hij a b hab
    apply geometricArtinStageToUnits_injective k₁ K₁ Ω₁ m₁ hz₁ i
    rw [← geometricArtinStageToUnits_transition k₁ K₁ Ω₁ m₁ hm₁ hz₁ i j hij a,
      ← geometricArtinStageToUnits_transition k₁ K₁ Ω₁ m₁ hm₁ hz₁ i j hij b, hab]
  · intro i hi
    exact (geometricArtinStageToUnits_injective k₂ K₂ Ω₂ m₂ hz₂ (q i)).comp
      (η i hi).injective

/-- Each target function reaches a common good degree and is lifted by
the inverse of the actual kernel equivalence at that degree. -/
theorem cofinalGeometricArtinTransportToUnits_surjective :
    Function.Surjective (cofinalGeometricArtinTransportToUnits
      k₁ K₁ Ω₁ k₂ K₂ Ω₂ m₁ m₂ hm₁ hm₂ hz₁ hz₂ i₀ η hη) := by
  let _ := geometricArtinDirectedSystem k₁ K₁ Ω₁ m₁ hm₁ hz₁
  let _ := geometricArtinDirectedSystem k₂ K₂ Ω₂ m₂ hm₂ hz₂
  apply DirectLimit.tailLift_surjective t₁ i₀
    (cofinalStageToUnits k₁ K₁ Ω₁ k₂ K₂ Ω₂ m₁ m₂ hz₂ i₀ η)
    (cofinalStageToUnits_transition k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₂ i₀ η hη)
  intro x
  obtain ⟨z, rfl⟩ := (e₂).surjective x
  induction z using DirectLimit.induction with
  | _ j a =>
      obtain ⟨i, rfl⟩ := (q).surjective j
      obtain ⟨l, hil, h₀l⟩ := exists_ge_ge i i₀
      refine ⟨l, h₀l, (η l h₀l).symm
        (t₂ (q i) (q l) ((q).monotone hil) a), ?_⟩
      change u₂ (q l) (η l h₀l ((η l h₀l).symm
        (t₂ (q i) (q l) ((q).monotone hil) a))) = u₂ (q i) a
      rw [MulEquiv.apply_symm_apply]
      exact geometricArtinStageToUnits_transition k₂ K₂ Ω₂ m₂ hm₂ hz₂
        (q i) (q l) ((q).monotone hil) a

/-- Multiplication on the exact original geometric function units,
constructed from good stages alone. -/
def cofinalGeometricArtinFunctionUnitsEquiv : G₁ˣ ≃* G₂ˣ :=
  (e₁).symm.trans (MulEquiv.ofBijective
    (cofinalGeometricArtinTransportToUnits k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ i₀ η hη)
    ⟨cofinalGeometricArtinTransportToUnits_injective k₁ K₁ Ω₁ k₂ K₂ Ω₂
        m₁ m₂ hm₁ hm₂ hz₁ hz₂ i₀ η hη,
      cofinalGeometricArtinTransportToUnits_surjective k₁ K₁ Ω₁ k₂ K₂ Ω₂
        m₁ m₂ hm₁ hm₂ hz₁ hz₂ i₀ η hη⟩)

/-- The resulting function map has the prescribed exact value at every
stage beyond the boundary-separating threshold. -/
theorem cofinalGeometricArtinFunctionUnitsEquiv_mk
    (i : I₁) (hi : i₀ ≤ i) (a : A₁ i) :
    cofinalGeometricArtinFunctionUnitsEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ i₀ η hη (e₁ ⟦⟨i, a⟩⟧) =
        e₂ ⟦⟨q i, η i hi a⟩⟧ := by
  let z : L₁ := ⟦⟨i, a⟩⟧
  exact (congrArg
    (cofinalGeometricArtinTransportToUnits k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ i₀ η hη)
    ((e₁).symm_apply_apply z)).trans
      (cofinalGeometricArtinTransportToUnits_mk k₁ K₁ Ω₁ k₂ K₂ Ω₂
        m₁ m₂ hm₁ hm₂ hz₁ hz₂ i₀ η hη i hi a)

/-- Every original geometric unit has a native representative beyond an
arbitrary prescribed finite stage. -/
theorem exists_geometricArtin_tail_representative (x : G₁ˣ) :
    ∃ (i : I₁) (_ : i₀ ≤ i) (a : A₁ i), e₁ ⟦⟨i, a⟩⟧ = x := by
  let _ := geometricArtinDirectedSystem k₁ K₁ Ω₁ m₁ hm₁ hz₁
  obtain ⟨z, rfl⟩ := (e₁).surjective x
  induction z using DirectLimit.induction with
  | _ i a =>
      obtain ⟨j, hij, h₀j⟩ := exists_ge_ge i i₀
      refine ⟨j, h₀j, t₁ i j hij a, ?_⟩
      exact geometricArtinStageToUnits_transition k₁ K₁ Ω₁ m₁ hm₁ hz₁ i j hij a

/-- Adding zero gives a multiplicative equivalence on the same original
geometric function fields. -/
def cofinalGeometricArtinFunctionEquiv : G₁ ≃* G₂ := by
  classical
  exact WithZero.withZeroUnitsEquiv.symm.trans
    ((MulEquiv.withZero (cofinalGeometricArtinFunctionUnitsEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ i₀ η hη)).trans WithZero.withZeroUnitsEquiv)

/-- Zero extension retains the same native geometric unit map. -/
theorem cofinalGeometricArtinFunctionEquiv_apply_units (x : G₁ˣ) :
    cofinalGeometricArtinFunctionEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ i₀ η hη (x : G₁) =
    (cofinalGeometricArtinFunctionUnitsEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ i₀ η hη x : G₂) := by
  classical
  change WithZero.withZeroUnitsEquiv
    (MulEquiv.withZero (cofinalGeometricArtinFunctionUnitsEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ i₀ η hη)
        (WithZero.withZeroUnitsEquiv.symm (x : G₁))) = _
  rw [WithZero.withZeroUnitsEquiv_symm_apply_coe]
  rfl

local notation "C₁" => separableClosure k₁ Ω₁

variable (eV : Place (separableClosure k₁ Ω₁) (geometricConstantExtension k₁ K₁ Ω₁) ≃
  Place (separableClosure k₂ Ω₂) (geometricConstantExtension k₂ K₂ Ω₂))

/-- Orders on the good finite stages determine every actual geometric
order, because every original function reaches one of those stages. -/
theorem cofinalGeometricArtinFunctionEquiv_order
    (horder : ∀ (i : I₁) (hi : i₀ ≤ i) (a : A₁ i) (W : Place C₁ G₁),
      (restrictedRayOrder (rayModulusBaseChange (geometricArtinStageField k₂ K₂ Ω₂ (q i)) m₂)
        (geometricArtinPlaceAtStage k₂ K₂ Ω₂ (q i) (eV W)) (η i hi a).val).toAdd =
      (restrictedRayOrder (rayModulusBaseChange (geometricArtinStageField k₁ K₁ Ω₁ i) m₁)
        (geometricArtinPlaceAtStage k₁ K₁ Ω₁ i W) a.val).toAdd)
    (x : G₁) (W : Place C₁ G₁) :
    (eV W).ord (cofinalGeometricArtinFunctionEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ i₀ η hη x) = W.ord x := by
  rcases GroupWithZero.eq_zero_or_unit x with rfl | ⟨u, rfl⟩
  · rw [map_zero, Place.ord_zero, Place.ord_zero]
  · rw [cofinalGeometricArtinFunctionEquiv_apply_units]
    obtain ⟨i, hi, a, rfl⟩ :=
      exists_geometricArtin_tail_representative k₁ K₁ Ω₁ m₁ hm₁ hz₁ i₀ u
    rw [cofinalGeometricArtinFunctionUnitsEquiv_mk
      k₁ K₁ Ω₁ k₂ K₂ Ω₂ m₁ m₂ hm₁ hm₂ hz₁ hz₂ i₀ η hη i hi,
      geometricArtinKernelEquiv_mk_order, geometricArtinKernelEquiv_mk_order]
    exact horder i hi a W

/-- Actual good-stage coordinates retain the full geometric
residue-value-one predicate at a reduced boundary. -/
theorem cofinalGeometricArtinFunctionEquiv_boundary
    (W : Place C₁ G₁)
    (hW₁ : m₁ (algebraicConstantPlaceRestrict (K := K₁) C₁ K₁ W) = 1)
    (hW₂ : m₂ (algebraicConstantPlaceRestrict (K := K₂)
      (separableClosure k₂ Ω₂) K₂ (eV W)) = 1)
    (hcoordinate : ∀ (i : I₁) (hi : i₀ ≤ i) (a : A₁ i),
      (η i hi a).val (geometricArtinPlaceAtStage k₂ K₂ Ω₂ (q i) (eV W)) = 1 ↔
        a.val (geometricArtinPlaceAtStage k₁ K₁ Ω₁ i W) = 1)
    (x : G₁) :
    (eV W).HasValue (cofinalGeometricArtinFunctionEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ i₀ η hη x) 1 ↔ W.HasValue x 1 := by
  rcases GroupWithZero.eq_zero_or_unit x with rfl | ⟨u, rfl⟩
  · rw [map_zero]
    exact ⟨fun h => False.elim (h.ne_zero one_ne_zero rfl),
      fun h => False.elim (h.ne_zero one_ne_zero rfl)⟩
  · rw [cofinalGeometricArtinFunctionEquiv_apply_units]
    obtain ⟨i, hi, a, rfl⟩ :=
      exists_geometricArtin_tail_representative k₁ K₁ Ω₁ m₁ hm₁ hz₁ i₀ u
    rw [cofinalGeometricArtinFunctionUnitsEquiv_mk
      k₁ K₁ Ω₁ k₂ K₂ Ω₂ m₁ m₂ hm₁ hm₂ hz₁ hz₂ i₀ η hη i hi]
    exact (geometricArtinKernelEquiv_mk_boundary k₂ K₂ Ω₂ m₂ hm₂ hz₂
      (q i) (η i hi a) (eV W) hW₂).symm.trans
        ((hcoordinate i hi a).trans
          (geometricArtinKernelEquiv_mk_boundary k₁ K₁ Ω₁ m₁ hm₁ hz₁ i a W hW₁))

end FunctionField.RayClass

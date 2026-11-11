/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricArtinBoundaryStages
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricArtinKernel
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricArtinKernelLocalization
public import Mathlib.Algebra.GroupWithZero.WithZero

/-!
# Transport of the original geometric Artin-kernel limit

This is the directed-limit construction for the original native Artin kernels.
The finite-stage arrows are not replaced by function-field arrows: the source
transition remains `geometricArtinTransition`, and the target is evaluated by
the original principal-kernel comparison. Compatible finite-stage kernel
equivalences therefore give a multiplicative equivalence of the actual
geometric constant composita, with their original constant factors retained.

The final comparisons compute normalized orders and the full residue-value-one
predicate directly on finite ray coordinates. Extraction of the finite-stage
arrows from a marked fundamental-group isomorphism belongs to the anabelian
assembly, not to this directed-limit construction.
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
local notation "L₁" => GeometricArtinKernel k₁ K₁ Ω₁ m₁ hm₁ hz₁
local notation "G₁" => geometricConstantExtension k₁ K₁ Ω₁
local notation "G₂" => geometricConstantExtension k₂ K₂ Ω₂
local notation "e₁" => geometricArtinKernelEquiv k₁ K₁ Ω₁ m₁ hm₁ hz₁
local notation "e₂" => geometricArtinKernelEquiv k₂ K₂ Ω₂ m₂ hm₂ hz₂
local notation "u₂" => geometricArtinStageToUnits k₂ K₂ Ω₂ m₂ hz₂

variable
    (η : ∀ i : GeometricArtinIndex k₁ K₁ Ω₁,
      GeometricArtinStageKernel k₁ K₁ Ω₁ m₁ i ≃*
        GeometricArtinStageKernel k₂ K₂ Ω₂ m₂
          (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ i))
    (hη : ∀ (i j : GeometricArtinIndex k₁ K₁ Ω₁) (hij : i ≤ j)
      (a : GeometricArtinStageKernel k₁ K₁ Ω₁ m₁ i),
      η j (geometricArtinTransition k₁ K₁ Ω₁ m₁ hm₁ i j hij a) =
        geometricArtinTransition k₂ K₂ Ω₂ m₂ hm₂
          (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ i)
          (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ j)
          ((geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂).monotone hij) (η i a))

/-- Evaluate a transported finite-stage Artin kernel in the target geometric units. -/
def transportedStageToUnits (i : I₁) : A₁ i →* G₂ˣ :=
  (u₂ (q i)).comp (η i).toMonoidHom

include hη in
theorem transportedStageToUnits_transition
    (i j : I₁) (hij : i ≤ j) (a : A₁ i) :
    transportedStageToUnits k₁ K₁ Ω₁ k₂ K₂ Ω₂ m₁ m₂ hz₂ η i a =
      transportedStageToUnits k₁ K₁ Ω₁ k₂ K₂ Ω₂ m₁ m₂ hz₂ η j (t₁ i j hij a) := by
  change u₂ (q i) (η i a) = u₂ (q j) (η j (t₁ i j hij a))
  rw [hη]
  exact (geometricArtinStageToUnits_transition k₂ K₂ Ω₂ m₂ hm₂ hz₂
    (q i) (q j) ((q).monotone hij) (η i a)).symm

/-- Evaluation of a compatible native kernel family in the actual target
geometric function units. -/
def geometricArtinTransportToUnits : L₁ →* G₂ˣ := by
  let _ := geometricArtinDirectedSystem k₁ K₁ Ω₁ m₁ hm₁ hz₁
  let g := transportedStageToUnits k₁ K₁ Ω₁ k₂ K₂ Ω₂ m₁ m₂ hz₂ η
  have hg := transportedStageToUnits_transition k₁ K₁ Ω₁ k₂ K₂ Ω₂
    m₁ m₂ hm₁ hm₂ hz₂ η hη
  exact
    { toFun := DirectLimit.lift t₁ (fun i => g i) hg
      map_one' := DirectLimit.lift_one g hg
      map_mul' := DirectLimit.lift_mul g hg }

/-- A native representative is evaluated through the same finite-stage arrow. -/
theorem geometricArtinTransportToUnits_mk (i : I₁) (a : A₁ i) :
    geometricArtinTransportToUnits k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη ⟦⟨i, a⟩⟧ = u₂ (q i) (η i a) := rfl

/-- Injectivity is checked in the original finite-stage kernel, through its
injective actual geometric function inclusion. -/
theorem geometricArtinTransportToUnits_injective :
    Function.Injective (geometricArtinTransportToUnits k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη) := by
  let _ := geometricArtinDirectedSystem k₁ K₁ Ω₁ m₁ hm₁ hz₁
  let g := transportedStageToUnits k₁ K₁ Ω₁ k₂ K₂ Ω₂ m₁ m₂ hz₂ η
  have hg := transportedStageToUnits_transition k₁ K₁ Ω₁ k₂ K₂ Ω₂
    m₁ m₂ hm₁ hm₂ hz₂ η hη
  exact DirectLimit.lift_injective t₁ (fun i => g i) hg (fun i =>
    (geometricArtinStageToUnits_injective k₂ K₂ Ω₂ m₂ hz₂ (q i)).comp (η i).injective)

/-- Every original target geometric unit comes from a target finite stage;
the degree correspondence and its finite-stage equivalence lift it back. -/
theorem geometricArtinTransportToUnits_surjective :
    Function.Surjective (geometricArtinTransportToUnits k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη) := by
  let _ := geometricArtinDirectedSystem k₁ K₁ Ω₁ m₁ hm₁ hz₁
  let _ := geometricArtinDirectedSystem k₂ K₂ Ω₂ m₂ hm₂ hz₂
  intro x
  obtain ⟨z, rfl⟩ := (e₂).surjective x
  induction z using DirectLimit.induction with
  | _ j a =>
      obtain ⟨i, rfl⟩ := (q).surjective j
      refine ⟨⟦⟨i, (η i).symm a⟩⟧, ?_⟩
      rw [geometricArtinTransportToUnits_mk, MulEquiv.apply_symm_apply]
      rfl

/-- The actual geometric function units transported through the original
Artin-kernel direct limit. -/
def geometricArtinFunctionUnitsEquiv : G₁ˣ ≃* G₂ˣ :=
  (e₁).symm.trans (MulEquiv.ofBijective
    (geometricArtinTransportToUnits k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη)
    ⟨geometricArtinTransportToUnits_injective k₁ K₁ Ω₁ k₂ K₂ Ω₂
        m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη,
      geometricArtinTransportToUnits_surjective k₁ K₁ Ω₁ k₂ K₂ Ω₂
        m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη⟩)

/-- The limit equivalence preserves the prescribed arrow on every original
finite-stage kernel representative. -/
theorem geometricArtinFunctionUnitsEquiv_mk (i : I₁) (a : A₁ i) :
    geometricArtinFunctionUnitsEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη (e₁ ⟦⟨i, a⟩⟧) = e₂ ⟦⟨q i, η i a⟩⟧ := by
  let z : L₁ := ⟦⟨i, a⟩⟧
  exact (congrArg
    (geometricArtinTransportToUnits k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη)
    ((e₁).symm_apply_apply z)).trans
      (geometricArtinTransportToUnits_mk k₁ K₁ Ω₁ k₂ K₂ Ω₂
        m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη i a)

/-- The prescribed native finite-stage values determine the geometric unit
map uniquely; choosing other representatives cannot change the result. -/
theorem geometricArtinFunctionUnitsEquiv_unique (ψ : G₁ˣ →* G₂ˣ)
    (hψ : ∀ (i : I₁) (a : A₁ i), ψ (e₁ ⟦⟨i, a⟩⟧) = e₂ ⟦⟨q i, η i a⟩⟧) :
    ψ = (geometricArtinFunctionUnitsEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη).toMonoidHom := by
  let _ := geometricArtinDirectedSystem k₁ K₁ Ω₁ m₁ hm₁ hz₁
  apply MonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := (e₁).surjective x
  induction a using DirectLimit.induction with
  | _ i a =>
      exact (hψ i a).trans
        (geometricArtinFunctionUnitsEquiv_mk k₁ K₁ Ω₁ k₂ K₂ Ω₂
          m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη i a).symm

/-- Extending by zero gives the multiplicative map on the exact geometric
function fields before using an additive reconstruction theorem. -/
def geometricArtinFunctionEquiv : G₁ ≃* G₂ := by
  classical
  exact WithZero.withZeroUnitsEquiv.symm.trans
    ((MulEquiv.withZero (geometricArtinFunctionUnitsEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη)).trans WithZero.withZeroUnitsEquiv)

/-- The extension by zero retains the reconstructed nonzero function. -/
theorem geometricArtinFunctionEquiv_apply_units (x : G₁ˣ) :
    geometricArtinFunctionEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη (x : G₁) =
      (geometricArtinFunctionUnitsEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂
        m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη x : G₂) := by
  classical
  change WithZero.withZeroUnitsEquiv
    (MulEquiv.withZero (geometricArtinFunctionUnitsEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη)
        (WithZero.withZeroUnitsEquiv.symm (x : G₁))) = _
  rw [WithZero.withZeroUnitsEquiv_symm_apply_coe]
  rfl

local notation "C₁" => separableClosure k₁ Ω₁

variable (eV : Place (separableClosure k₁ Ω₁) (geometricConstantExtension k₁ K₁ Ω₁) ≃
  Place (separableClosure k₂ Ω₂) (geometricConstantExtension k₂ K₂ Ω₂))

/-- Exact finite-stage orders give exact normalized orders for every actual
geometric function, independently of its native representative. -/
theorem geometricArtinFunctionEquiv_order
    (horder : ∀ (i : I₁) (a : A₁ i) (W : Place C₁ G₁),
      (restrictedRayOrder (rayModulusBaseChange (geometricArtinStageField k₂ K₂ Ω₂ (q i)) m₂)
        (geometricArtinPlaceAtStage k₂ K₂ Ω₂ (q i) (eV W)) (η i a).val).toAdd =
      (restrictedRayOrder (rayModulusBaseChange (geometricArtinStageField k₁ K₁ Ω₁ i) m₁)
        (geometricArtinPlaceAtStage k₁ K₁ Ω₁ i W) a.val).toAdd)
    (x : G₁) (W : Place C₁ G₁) :
    (eV W).ord (geometricArtinFunctionEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη x) = W.ord x := by
  let _ := geometricArtinDirectedSystem k₁ K₁ Ω₁ m₁ hm₁ hz₁
  rcases GroupWithZero.eq_zero_or_unit x with rfl | ⟨u, rfl⟩
  · rw [map_zero, Place.ord_zero, Place.ord_zero]
  · rw [geometricArtinFunctionEquiv_apply_units]
    obtain ⟨a, rfl⟩ := (e₁).surjective u
    induction a using DirectLimit.induction with
    | _ i a =>
        rw [geometricArtinFunctionUnitsEquiv_mk,
          geometricArtinKernelEquiv_mk_order, geometricArtinKernelEquiv_mk_order]
        exact horder i a W

/-- At an original reduced boundary, finite-coordinate preservation detects
the full geometric principal-unit predicate, including the zero case. -/
theorem geometricArtinFunctionEquiv_boundary
    (W : Place C₁ G₁)
    (hW₁ : m₁ (algebraicConstantPlaceRestrict (K := K₁) C₁ K₁ W) = 1)
    (hW₂ : m₂ (algebraicConstantPlaceRestrict (K := K₂)
      (separableClosure k₂ Ω₂) K₂ (eV W)) = 1)
    (hcoordinate : ∀ (i : I₁) (a : A₁ i),
      (η i a).val (geometricArtinPlaceAtStage k₂ K₂ Ω₂ (q i) (eV W)) = 1 ↔
        a.val (geometricArtinPlaceAtStage k₁ K₁ Ω₁ i W) = 1)
    (x : G₁) :
    (eV W).HasValue (geometricArtinFunctionEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ η hη x) 1 ↔ W.HasValue x 1 := by
  let _ := geometricArtinDirectedSystem k₁ K₁ Ω₁ m₁ hm₁ hz₁
  rcases GroupWithZero.eq_zero_or_unit x with rfl | ⟨u, rfl⟩
  · rw [map_zero]
    exact ⟨fun h => False.elim (h.ne_zero one_ne_zero rfl),
      fun h => False.elim (h.ne_zero one_ne_zero rfl)⟩
  · rw [geometricArtinFunctionEquiv_apply_units]
    obtain ⟨a, rfl⟩ := (e₁).surjective u
    induction a using DirectLimit.induction with
    | _ i a =>
        rw [geometricArtinFunctionUnitsEquiv_mk]
        exact (geometricArtinKernelEquiv_mk_boundary k₂ K₂ Ω₂ m₂ hm₂ hz₂
          (q i) (η i a) (eV W) hW₂).symm.trans
            ((hcoordinate i a).trans
              (geometricArtinKernelEquiv_mk_boundary k₁ K₁ Ω₁ m₁ hm₁ hz₁ i a W hW₁))

end FunctionField.RayClass

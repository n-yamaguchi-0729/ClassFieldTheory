/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayUnitSeparation
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayTransport
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayBaseChange
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayDegree

/-!
# Extracting actual base-change coherence from the original Artin square

For coordinatewise maps of actual local ray factors, the original
place-restriction square and the actual ramification indices determine
the order of either composite through finite extension.

On each original one-place generator both composites are supported in
the same whole restriction fibre. An original positive boundary outside
that fibre supplies an anchor. The actual Artin kernel then proves
equality before reciprocity. Multiplicative induction extends this to
every actual restricted family.

Only the equality after original reciprocity is used in the separation
step; no compatibility of local multiplicative maps or of function units
is assumed.
-/

@[expose] public section

universe u₁ v₁ w₁ u₂ v₂ w₂

noncomputable section

open AlgebraicCurve

namespace FunctionField.RayClass

section CoordinateOrders

variable {k₁ K₁ L₁ k₂ K₂ L₂ : Type*}
    [Field k₁] [Field K₁] [Field L₁]
    [Algebra k₁ K₁] [Algebra k₁ L₁] [Algebra K₁ L₁]
    [IsScalarTower k₁ K₁ L₁] [FiniteDimensional K₁ L₁]
    [Field k₂] [Field K₂] [Field L₂]
    [Algebra k₂ K₂] [Algebra k₂ L₂] [Algebra K₂ L₂]
    [IsScalarTower k₂ K₂ L₂] [FiniteDimensional K₂ L₂]
    (m₁ : Modulus k₁ K₁) (m₂ : Modulus k₂ K₂)
    (hm₁ : ∀ v, m₁ v ≤ 1) (hm₂ : ∀ v, m₂ v ≤ 1)
    (e : Place k₁ K₁ ≃ Place k₂ K₂)
    (eL : Place k₁ L₁ ≃ Place k₂ L₂)
    (hplaces : ∀ w : Place k₁ L₁, (eL w).restrict K₂ = e (w.restrict K₁))
    (φ : ∀ v, RayLocalFactor m₁ v ≃* RayLocalFactor m₂ (e v))
    (ψ : ∀ w, RayLocalFactor (rayModulusBaseChange L₁ m₁) w ≃*
      RayLocalFactor (rayModulusBaseChange L₂ m₂) (eL w))

local notation "M₁" => rayModulusBaseChange L₁ m₁
local notation "M₂" => rayModulusBaseChange L₂ m₂
local notation "ρ" => restrictedRayEquiv e φ
local notation "ρL" => restrictedRayEquiv eL ψ

include hplaces in
/-- The two actual finite-extension composites have the same normalized
order whenever their local maps preserve order and their original
ramification indices agree. -/
theorem restrictedRayEquiv_baseChange_order
    (hφ : ∀ v a, localRayFactorOrder m₂ (e v) (φ v a) = localRayFactorOrder m₁ v a)
    (hψ : ∀ w a, localRayFactorOrder M₂ (eL w) (ψ w a) = localRayFactorOrder M₁ w a)
    (hindex : ∀ w : Place k₁ L₁, w.ramificationIndex K₁ = (eL w).ramificationIndex K₂)
    (a : RayRestrictedProduct m₁) (w : Place k₁ L₁) :
    localRayFactorOrder M₂ (eL w)
        (ρL (restrictedRayBaseChange (L := L₁) m₁ hm₁ a) (eL w)) =
      localRayFactorOrder M₂ (eL w)
        (restrictedRayBaseChange (L := L₂) m₂ hm₂ (ρ a) (eL w)) := by
  apply Multiplicative.ext
  rw [restrictedRayEquiv_apply,
    hψ w (restrictedRayBaseChange (L := L₁) m₁ hm₁ a w),
    restrictedRayBaseChange_apply, localRayFactorOrder_baseChange,
    restrictedRayBaseChange_apply, localRayFactorOrder_baseChange,
    hplaces w, restrictedRayEquiv_apply, hφ, hindex w]

include hplaces in
/-- Transport of the actual base-changed one-place family is supported
over the matched original lower place. -/
theorem restrictedRayEquiv_baseChange_single_support
    (v : Place k₁ K₁) (x : RayLocalFactor m₁ v)
    (W : Place k₂ L₂) (hW : W.restrict K₂ ≠ e v) :
    ρL (restrictedRayBaseChange (L := L₁) m₁ hm₁
      (localRayToRestrictedProduct m₁ v x)) W = 1 := by
  obtain ⟨w, rfl⟩ := eL.surjective W
  have hw : w.restrict K₁ ≠ v := by
    intro h
    apply hW
    rw [hplaces w, h]
  rw [restrictedRayEquiv_apply,
    restrictedRayBaseChange_single_of_restrict_ne m₁ hm₁ v x w hw, map_one]

/-- Base change of the transported actual one-place family has the same
support restriction, through the literal lower local map. -/
theorem restrictedRayEquiv_single_baseChange_support
    (v : Place k₁ K₁) (x : RayLocalFactor m₁ v)
    (W : Place k₂ L₂) (hW : W.restrict K₂ ≠ e v) :
    restrictedRayBaseChange (L := L₂) m₂ hm₂
      (ρ (localRayToRestrictedProduct m₁ v x)) W = 1 := by
  rw [restrictedRayEquiv_local]
  exact restrictedRayBaseChange_single_of_restrict_ne m₂ hm₂ (e v) (φ v x) W hW

end CoordinateOrders

section ReciprocitySeparation

variable {k₁ : Type u₁} {K₁ : Type v₁} {L₁ : Type w₁}
    {k₂ : Type u₂} {K₂ : Type v₂} {L₂ : Type w₂}
    [Field k₁] [Field K₁] [Field L₁]
    [Algebra k₁ K₁] [Algebra k₁ L₁] [Algebra K₁ L₁]
    [IsScalarTower k₁ K₁ L₁] [FiniteDimensional K₁ L₁]
    [Field k₂] [Finite k₂] [Field K₂] [Field L₂]
    [Algebra k₂ K₂] [Algebra k₂ L₂] [Algebra K₂ L₂]
    [IsScalarTower k₂ K₂ L₂] [FiniteDimensional K₂ L₂]
    [Algebra (RatFunc k₂) L₂] [IsScalarTower k₂ (RatFunc k₂) L₂]
    [FunctionField k₂ L₂] [HasPrincipalDivisors k₂ L₂]
    (m₁ : Modulus k₁ K₁) (m₂ : Modulus k₂ K₂)
    (hm₁ : ∀ v, m₁ v ≤ 1) (hm₂ : ∀ v, m₂ v ≤ 1)
    (e : Place k₁ K₁ ≃ Place k₂ K₂)
    (eL : Place k₁ L₁ ≃ Place k₂ L₂)
    (hplaces : ∀ w : Place k₁ L₁, (eL w).restrict K₂ = e (w.restrict K₁))
    (φ : ∀ v, RayLocalFactor m₁ v ≃* RayLocalFactor m₂ (e v))
    (ψ : ∀ w, RayLocalFactor (rayModulusBaseChange L₁ m₁) w ≃*
      RayLocalFactor (rayModulusBaseChange L₂ m₂) (eL w))

local notation "M₁" => rayModulusBaseChange L₁ m₁
local notation "M₂" => rayModulusBaseChange L₂ m₂
local notation "ρ" => restrictedRayEquiv e φ
local notation "ρL" => restrictedRayEquiv eL ψ
local notation "b₁" => restrictedRayBaseChange (L := L₁) m₁ hm₁
local notation "b₂" => restrictedRayBaseChange (L := L₂) m₂ hm₂

include hplaces in
/-- The original Artin-image square forces actual finite-extension
coherence of the whole coordinatewise ray maps. The proof extracts each
supported one-place family using its actual orders and another boundary. -/
theorem restrictedRayEquiv_baseChange_of_artin_square
    (hφ : ∀ v a, localRayFactorOrder m₂ (e v) (φ v a) = localRayFactorOrder m₁ v a)
    (hψ : ∀ w a, localRayFactorOrder M₂ (eL w) (ψ w a) = localRayFactorOrder M₁ w a)
    (hindex : ∀ w : Place k₁ L₁, w.ramificationIndex K₁ = (eL w).ramificationIndex K₂)
    (hboundary : ∀ v : Place k₂ K₂, ∃ z : Place k₂ K₂, z ≠ v ∧ m₂ z ≠ 0)
    (hartin : (restrictedProductAbsoluteArtin M₂).comp ((ρL).toMonoidHom.comp b₁) =
      (restrictedProductAbsoluteArtin M₂).comp ((b₂).comp (ρ).toMonoidHom)) :
    (ρL).toMonoidHom.comp b₁ = (b₂).comp (ρ).toMonoidHom := by
  apply restrictedRay_hom_ext m₁
  intro v x
  let a := localRayToRestrictedProduct m₁ v x
  let b := ρL (b₁ a)
  let c := b₂ (ρ a)
  have hArtin : restrictedProductAbsoluteArtin M₂ b =
      restrictedProductAbsoluteArtin M₂ c :=
    DFunLike.congr_fun hartin a
  have horder (W : Place k₂ L₂) :
      localRayFactorOrder M₂ W (b W) = localRayFactorOrder M₂ W (c W) := by
    obtain ⟨w, rfl⟩ := eL.surjective W
    exact restrictedRayEquiv_baseChange_order m₁ m₂ hm₁ hm₂ e eL hplaces φ ψ
      hφ hψ hindex a w
  have hb (W : Place k₂ L₂) (hW : W.restrict K₂ ≠ e v) : b W = 1 :=
    restrictedRayEquiv_baseChange_single_support m₁ m₂ hm₁ e eL hplaces ψ v x W hW
  have hc (W : Place k₂ L₂) (hW : W.restrict K₂ ≠ e v) : c W = 1 :=
    restrictedRayEquiv_single_baseChange_support m₁ m₂ hm₂ e φ v x W hW
  obtain ⟨W, hWv, hWm⟩ :=
    exists_boundary_outside_restriction_fibre (L := L₂) m₂ (e v) (hboundary (e v))
  exact restrictedRay_eq_of_artin_order_anchor M₂ b c hArtin horder W hWm
    ((hb W hWv).trans (hc W hWv).symm)

end ReciprocitySeparation

end FunctionField.RayClass

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.OrbitActions
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.DecompositionHilbert90
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.CompactUnits

/-!
# Integral orbit blocks

The everywhere-integral idele group is an unrestricted product of its integral
fiber blocks. Each block is the module induced from the actual integral units
at any place above that base place. These comparisons respect the actual action.
-/

noncomputable section

namespace FunctionField.IdeleGroup

open AlgebraicCurve ProCGroups.InducedFunctions
open scoped AlgebraicCurve.Place

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]

private theorem smul_mem_fiberIntegralUnits (v : Place k K) (σ : L ≃ₐ[K] L)
    (a : fiberIntegralUnits (L := L) v) : σ • a.val ∈ fiberIntegralUnits (L := L) v := by
  obtain ⟨w, rfl⟩ := Place.exists_restrict_eq (M := L) v
  apply (fiberInducedEquiv_integral_iff (K := K) w _).mp
  rw [fiberInducedEquiv_smul]
  exact fun τ => (fiberInducedEquiv_integral_iff (K := K) w a.val).mpr a.2 (τ * σ)

/-- The actual Galois action restricts to the integral fiber block. -/
instance fiberIntegralUnitsAction (v : Place k K) :
    MulDistribMulAction (L ≃ₐ[K] L) (fiberIntegralUnits (L := L) v) where
  smul σ a := ⟨σ • a.val, smul_mem_fiberIntegralUnits v σ a⟩
  one_smul a := Subtype.ext (one_smul _ a.val)
  mul_smul σ τ a := Subtype.ext (mul_smul σ τ a.val)
  smul_one σ := Subtype.ext (smul_one σ)
  smul_mul σ a b := Subtype.ext (smul_mul' σ a.val b.val)

/-- Evaluate conjugates of an integral block in the actual induced integral-unit module. -/
def integralFiberToInduced (w : Place k L) :
    fiberIntegralUnits (L := L) (w.restrict K) →*
      InducedModule (B := w.adicCompletionIntegers.units) (decompositionGroup (K := K) w) where
  toFun a := ⟨fun σ => ⟨(fiberInducedEquiv (K := K) w a.val).val σ,
      (fiberInducedEquiv_integral_iff (K := K) w a.val).mpr a.2 σ⟩,
    fun h σ => Subtype.ext ((fiberInducedEquiv (K := K) w a.val).2 h σ)⟩
  map_one' := by
    apply Subtype.ext
    funext σ
    apply Subtype.ext
    exact congrArg (fun f => f.val σ) (map_one (fiberInducedEquiv (K := K) w))
  map_mul' a b := by
    apply Subtype.ext
    funext σ
    apply Subtype.ext
    exact congrArg (fun f => f.val σ) (map_mul (fiberInducedEquiv (K := K) w) a.val b.val)

theorem integralFiberToInduced_bijective (w : Place k L) :
    Function.Bijective (integralFiberToInduced (K := K) w) := by
  constructor
  · intro a b h
    apply Subtype.ext
    apply (fiberInducedEquiv (K := K) w).injective
    apply Subtype.ext
    funext σ
    exact congrArg (fun f => (f.val σ).val) h
  · intro f
    let f' : InducedModule (B := w.adicCompletionˣ) (decompositionGroup (K := K) w) :=
      ⟨fun σ => (f.val σ).val, fun h σ => congrArg Subtype.val (f.2 h σ)⟩
    let a := (fiberInducedEquiv (K := K) w).symm f'
    have ha : a ∈ fiberIntegralUnits (L := L) (w.restrict K) := by
      apply (fiberInducedEquiv_integral_iff (K := K) w a).mp
      change ∀ σ, ((fiberInducedEquiv (K := K) w)
        ((fiberInducedEquiv (K := K) w).symm f')).val σ ∈ w.adicCompletionIntegers.units
      rw [MulEquiv.apply_symm_apply]
      exact fun σ => (f.val σ).2
    refine ⟨⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    funext σ
    apply Subtype.ext
    exact congrArg (fun b => b.val σ) ((fiberInducedEquiv (K := K) w).apply_symm_apply f')

/-- Integral fiber blocks are induced from the actual integral units of a completion. -/
def integralFiberInducedEquiv (w : Place k L) :
    fiberIntegralUnits (L := L) (w.restrict K) ≃*
      InducedModule (B := w.adicCompletionIntegers.units) (decompositionGroup (K := K) w) :=
  MulEquiv.ofBijective (integralFiberToInduced (K := K) w)
    (integralFiberToInduced_bijective (K := K) w)

/-- The integral block comparison preserves the actual global Galois action. -/
theorem integralFiberInducedEquiv_smul (w : Place k L) (σ : L ≃ₐ[K] L)
    (a : fiberIntegralUnits (L := L) (w.restrict K)) :
    integralFiberInducedEquiv (K := K) w (σ • a) =
      σ • integralFiberInducedEquiv (K := K) w a := by
  apply Subtype.ext
  funext τ
  apply Subtype.ext
  exact congrArg (fun f => f.val τ) (fiberInducedEquiv_smul (K := K) w σ a.val)

/-- The everywhere-integral idele group is the product of all its integral fibers. -/
def integralGroupByPlace : integralSubgroup (k := k) (K := L) ≃*
    (∀ v : Place k K, fiberIntegralUnits (L := L) v) where
  toFun a v := ⟨fiberProjection (L := L) v a.val, fun u => a.2 u.val⟩
  invFun a := ⟨(groupByPlace (k := k) (K := K) (L := L)).symm
    ⟨fun v => (a v).val, Filter.Eventually.of_forall fun v => (a v).2⟩,
    fun u => (a (u.restrict K)).2 ⟨u, Place.restrict_mem_fiberOver u⟩⟩
  left_inv a := Subtype.ext rfl
  right_inv a := by
    funext v
    apply Subtype.ext
    have h := (groupByPlace (k := k) (K := K) (L := L)).apply_symm_apply
      ⟨fun v => (a v).val, Filter.Eventually.of_forall fun v => (a v).2⟩
    exact congrArg (fun b => b v) h
  map_mul' _ _ := rfl

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem smul_mem_integralSubgroup (σ : L ≃ₐ[K] L)
    (a : integralSubgroup (k := k) (K := L)) :
    σ • a.val ∈ integralSubgroup (k := k) (K := L) := by
  apply (divisor_eq_one_iff _).mp
  apply Multiplicative.ext
  rw [smul_algAut_eq_semilinear, divisor_smul, (divisor_eq_one_iff a.val).mpr a.2]
  exact smul_zero _

/-- Galois automorphisms preserve everywhere-integral ideles. -/
instance integralGaloisAction :
    MulDistribMulAction (L ≃ₐ[K] L) (integralSubgroup (k := k) (K := L)) where
  smul σ a := ⟨σ • a.val, smul_mem_integralSubgroup σ a⟩
  one_smul a := Subtype.ext (one_smul _ a.val)
  mul_smul σ τ a := Subtype.ext (mul_smul σ τ a.val)
  smul_one σ := Subtype.ext (smul_one σ)
  smul_mul σ a b := Subtype.ext (smul_mul' σ a.val b.val)

/-- Regrouping integral ideles is equivariant for the actual fiber actions. -/
theorem integralGroupByPlace_smul (σ : L ≃ₐ[K] L)
    (a : integralSubgroup (k := k) (K := L)) (v : Place k K) :
    integralGroupByPlace (k := k) (K := K) (L := L) (σ • a) v =
      σ • integralGroupByPlace (k := k) (K := K) (L := L) a v := by
  apply Subtype.ext
  exact fiberProjection_smul (L := L) v σ a.val

end FunctionField.IdeleGroup

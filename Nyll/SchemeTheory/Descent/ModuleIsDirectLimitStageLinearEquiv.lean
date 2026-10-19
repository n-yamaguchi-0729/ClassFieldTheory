/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_IsDirectLimit_exists_stage_linearEquiv_of_finitePresentation_compat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Descent.ModuleIsDirectLimitLinearEquiv
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Data.Finset.Order
import Mathlib.Order.Directed
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext

/-!
# Compatible descent of linear equivalences

Descends a linear equivalence of finitely presented modules to a compatible finite stage.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Module_IsDirectLimit_exists_stage_linearEquiv_of_finitePresentation_compat

open TensorProduct

universe u v w

theorem _root_.Module.IsDirectLimit.exists_stage_linearEquiv_of_finitePresentation_compat
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {B₀ : Type u} [CommRing B₀]
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra B₀ (B i)]
    (τ : ∀ i j, i ≤ j → B i →ₐ[B₀] B j) [DirectedSystem B (fun i j h => τ i j h)]
    (Bω : Type u) [CommRing Bω] [Algebra B₀ Bω] (g : ∀ i, B i →ₐ[B₀] Bω)
    (hg : ∀ i j (h : i ≤ j), (g j).comp (τ i j h) = g i)
    (hsurj : ∀ b : Bω, ∃ i x, g i x = b)
    (hzero : ∀ i (x : B i), g i x = 0 → ∃ (j : ι) (h : i ≤ j), τ i j h x = 0)
    (i₀ : ι) [Algebra (B i₀) Bω] (hgi : ∀ x, algebraMap (B i₀) Bω x = g i₀ x)
    (P Q : Type w) [AddCommGroup P] [Module (B i₀) P] [AddCommGroup Q] [Module (B i₀) Q]
    [Module.FinitePresentation (B i₀) P] [Module.FinitePresentation (B i₀) Q]
    (e : TensorProduct (B i₀) Bω P ≃ₗ[Bω] TensorProduct (B i₀) Bω Q) :
    ∃ (j : ι) (hj : i₀ ≤ j) (gj : letI := (τ i₀ j hj).toRingHom.toAlgebra; B j →ₐ[B
      i₀] Bω) (_ : ∀ b, gj b = g j b)
      (ej : letI := (τ i₀ j hj).toRingHom.toAlgebra; TensorProduct (B i₀) (B j) P
        ≃ₗ[B j] TensorProduct (B i₀) (B j) Q),
      letI := (τ i₀ j hj).toRingHom.toAlgebra
      ∀ x : TensorProduct (B i₀) (B j) P, e (gj.toLinearMap.rTensor P x) =
        gj.toLinearMap.rTensor Q (ej x) := by
  let ι' := {j : ι // i₀ ≤ j}
  let : Nonempty ι' := ⟨⟨i₀, le_rfl⟩⟩
  have : IsDirectedOrder ι' := ⟨fun a b => by
    obtain ⟨k, h1, h2⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨k, a.2.trans h1⟩, h1, h2⟩⟩
  let B' : ι' → Type u := fun j => B j.1
  let algj : ∀ j : ι', Algebra (B i₀) (B' j) := fun j => (τ i₀ j.1 j.2).toRingHom.toAlgebra
  let τ' : ∀ j k : ι', j ≤ k → B' j →ₐ[B i₀] B' k := fun j k h =>
    { (τ j.1 k.1 h).toRingHom with
      commutes' := fun b => by
        change τ j.1 k.1 h (τ i₀ j.1 j.2 b) = τ i₀ k.1 k.2 b
        exact DirectedSystem.map_map (f := fun i j h => ⇑(τ i j h)) j.2 h b }
  have : DirectedSystem B' (fun j k h => τ' j k h) :=
    ⟨fun j x => DirectedSystem.map_self (f := fun i j h => ⇑(τ i j h)) x,
     fun a b c h1 h2 x => DirectedSystem.map_map (f := fun i j h => ⇑(τ i j h)) h1 h2 x⟩
  let g' : ∀ j : ι', B' j →ₐ[B i₀] Bω := fun j =>
    { (g j.1).toRingHom with
      commutes' := fun b => by
        change g j.1 (τ i₀ j.1 j.2 b) = algebraMap (B i₀) Bω b
        rw [hgi, ← AlgHom.comp_apply, hg] }
  have hg' : ∀ j k (h : j ≤ k), (g' k).comp (τ' j k h) = g' j := fun j k h =>
    AlgHom.ext fun x => by
      change g k.1 (τ j.1 k.1 h x) = g j.1 x
      rw [← AlgHom.comp_apply, hg]
  have hsurj' : ∀ b : Bω, ∃ j x, g' j x = b := fun b => by
    obtain ⟨i₁, x, rfl⟩ := hsurj b
    obtain ⟨k, h1, h2⟩ := directed_of (· ≤ ·) i₀ i₁
    refine ⟨⟨k, h1⟩, τ i₁ k h2 x, ?_⟩
    change g k (τ i₁ k h2 x) = g i₁ x
    rw [← AlgHom.comp_apply, hg]
  have hzero' : ∀ j (x : B' j), g' j x = 0 → ∃ (k : ι') (h : j ≤ k), τ' j k h x = 0 :=
    fun j x hx => by
      obtain ⟨k, hjk, hk⟩ := hzero j.1 x hx
      exact ⟨⟨k, j.2.trans hjk⟩, hjk, hk⟩
  obtain ⟨j, eⱼ, hsq⟩ :=
    Module.IsDirectLimit.exists_linearEquiv_of_finitePresentation
      B' τ' Bω g' hg' hsurj' hzero' P Q e
  refine ⟨j.1, j.2, g' j, fun b => rfl, eⱼ, fun x => ?_⟩
  exact LinearMap.congr_fun hsq x
end Module_IsDirectLimit_exists_stage_linearEquiv_of_finitePresentation_compat
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation

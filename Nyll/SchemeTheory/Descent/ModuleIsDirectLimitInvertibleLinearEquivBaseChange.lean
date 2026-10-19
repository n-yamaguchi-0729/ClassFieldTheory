/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_IsDirectLimit_exists_invertible_linearEquiv_baseChange.lean
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
# Descent of invertible modules along direct limits

Descends invertibility and linear equivalences after base change to a finite stage.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Module_IsDirectLimit_exists_invertible_linearEquiv_baseChange

open TensorProduct

namespace S17LFP

open _root_.AlgebraicCurves.Foundations.Algebra.Proofs
open Module_IsDirectLimit_exists_linearEquiv_of_finitePresentation.S17LFP

section Descent

universe u v w

variable {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  {B₀ : Type u} [CommRing B₀]
  (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra B₀ (B i)]
  (τ : ∀ i j, i ≤ j → B i →ₐ[B₀] B j) [DirectedSystem B (fun i j h => τ i j h)]
  (Bω : Type u) [CommRing Bω] [Algebra B₀ Bω] (g : ∀ i, B i →ₐ[B₀] Bω)
  (hg : ∀ i j (h : i ≤ j), (g j).comp (τ i j h) = g i)
  (hsurj : ∀ b : Bω, ∃ i x, g i x = b)
  (hzero : ∀ i (x : B i), g i x = 0 → ∃ (j : ι) (h : i ≤ j), τ i j h x = 0)
  (P Q : Type*) [AddCommGroup P] [Module B₀ P] [AddCommGroup Q] [Module B₀ Q]

include hg hsurj hzero in
theorem inv_obj (Y : Type*) [AddCommGroup Y] [Module Bω Y] [Module.Invertible Bω Y] :
    ∃ (i : ι) (L : Type u) (_ : AddCommGroup L) (_ : Module (B i) L),
      Module.Invertible (B i) L ∧
      Nonempty (letI := (g i).toRingHom.toAlgebra; Bω ⊗[B i] L ≃ₗ[Bω] Y) := by
  have : Module.FinitePresentation Bω Y := Module.finitePresentation_of_projective _ _
  have : Module.FinitePresentation Bω (Module.Dual Bω Y) :=
    Module.finitePresentation_of_projective _ _
  obtain ⟨i₁, L₁, _, _, hL₁, ⟨eL⟩⟩ := obj B τ Bω g hg hsurj Y
  obtain ⟨i₂, D₂, _, _, hD₂, ⟨eD⟩⟩ := obj B τ Bω g hg hsurj (Module.Dual Bω Y)
  have := hL₁
  have := hD₂
  obtain ⟨i, h₁, h₂⟩ := _root_.exists_ge_ge i₁ i₂
  let aω₁ : Algebra (B i₁) Bω := (g i₁).toRingHom.toAlgebra
  let aω₂ : Algebra (B i₂) Bω := (g i₂).toRingHom.toAlgebra
  let aω : Algebra (B i) Bω := (g i).toRingHom.toAlgebra
  let a₁ : Algebra (B i₁) (B i) := (τ i₁ i h₁).toRingHom.toAlgebra
  let a₂ : Algebra (B i₂) (B i) := (τ i₂ i h₂).toRingHom.toAlgebra
  have : IsScalarTower (B i₁) (B i) Bω := IsScalarTower.of_algebraMap_eq fun x => by
    change g i₁ x = g i (τ i₁ i h₁ x)
    rw [← AlgHom.comp_apply, hg]
  have : IsScalarTower (B i₂) (B i) Bω := IsScalarTower.of_algebraMap_eq fun x => by
    change g i₂ x = g i (τ i₂ i h₂ x)
    rw [← AlgHom.comp_apply, hg]
  let Lᵢ := B i ⊗[B i₁] L₁
  let Dᵢ := B i ⊗[B i₂] D₂
  let eLᵢ : Bω ⊗[B i] Lᵢ ≃ₗ[Bω] Y :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange (B i₁) (B i) Bω Bω L₁ ≪≫ₗ eL
  let eDᵢ : Bω ⊗[B i] Dᵢ ≃ₗ[Bω] Module.Dual Bω Y :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange (B i₂) (B i) Bω Bω D₂ ≪≫ₗ eD
  have := finitePresentation_tensorProduct (R := B i) Lᵢ Dᵢ
  let e : Bω ⊗[B i] (Lᵢ ⊗[B i] Dᵢ) ≃ₗ[Bω] Bω ⊗[B i] B i :=
    TensorProduct.AlgebraTensorModule.distribBaseChange (B i) Bω Lᵢ Dᵢ ≪≫ₗ
      TensorProduct.congr eLᵢ eDᵢ ≪≫ₗ
      (TensorProduct.comm _ _ _ ≪≫ₗ Module.Invertible.linearEquiv Bω Y) ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.rid (B i) Bω Bω).symm
  obtain ⟨j, hij, ⟨eⱼ⟩⟩ := iso_desc_stage B τ Bω g hg hsurj hzero (Lᵢ ⊗[B i] Dᵢ) (B i) e
  let aj : Algebra (B i) (B j) := (τ i j hij).toRingHom.toAlgebra
  let aωj : Algebra (B j) Bω := (g j).toRingHom.toAlgebra
  have : IsScalarTower (B i) (B j) Bω := IsScalarTower.of_algebraMap_eq fun x => by
    change g i x = g j (τ i j hij x)
    rw [← AlgHom.comp_apply, hg]
  let f : (B j ⊗[B i] Lᵢ) ⊗[B j] (B j ⊗[B i] Dᵢ) ≃ₗ[B j] B j :=
    (TensorProduct.AlgebraTensorModule.distribBaseChange (B i) (B j) Lᵢ Dᵢ).symm ≪≫ₗ
      eⱼ ≪≫ₗ TensorProduct.AlgebraTensorModule.rid (B i) (B j) (B j)
  refine ⟨j, B j ⊗[B i] Lᵢ, inferInstance, inferInstance, Module.Invertible.left f, ⟨?_⟩⟩
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange (B i) (B j) Bω Bω Lᵢ ≪≫ₗ eLᵢ

end Descent

end S17LFP

universe u v w

theorem _root_.Module.IsDirectLimit.exists_invertible_linearEquiv_baseChange
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {B₀ : Type u} [CommRing B₀]
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra B₀ (B i)]
    (τ : ∀ i j, i ≤ j → B i →ₐ[B₀] B j) [DirectedSystem B (fun i j h => τ i j h)]
    (Bω : Type u) [CommRing Bω] [Algebra B₀ Bω] (g : ∀ i, B i →ₐ[B₀] Bω)
    (hg : ∀ i j (h : i ≤ j), (g j).comp (τ i j h) = g i)
    (hsurj : ∀ b : Bω, ∃ i x, g i x = b)
    (hzero : ∀ i (x : B i), g i x = 0 → ∃ (j : ι) (h : i ≤ j), τ i j h x = 0)
    (Y : Type w) [AddCommGroup Y] [Module Bω Y] [Module.Invertible Bω Y] :
    ∃ (i : ι) (L : Type u) (_ : AddCommGroup L) (_ : Module (B i) L),
      Module.Invertible (B i) L ∧
      Nonempty (letI := (g i).toRingHom.toAlgebra; TensorProduct (B i) Bω L ≃ₗ[Bω] Y) :=
  S17LFP.inv_obj B τ Bω g hg hsurj hzero Y
end Module_IsDirectLimit_exists_invertible_linearEquiv_baseChange
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation

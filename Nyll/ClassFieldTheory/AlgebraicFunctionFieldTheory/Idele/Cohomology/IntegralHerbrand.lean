/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.IntegralHerbrand
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.IntegralOrbitBlocks
import Nyll.AlgebraicCurves.Places.Ramification.FiniteRamification
import Nyll.GaloisCohomology.Cyclic.Herbrand.AlmostTrivialProduct

/-!
# Herbrand quotients of integral idele blocks

Shapiro's explicit equivalences transfer the actual local integral-unit calculation
to each base-place fiber. Only the finitely many ramified fibers have nontrivial
low-degree Tate groups.
-/

noncomputable section

namespace FunctionField.IdeleGroup

open AlgebraicCurve CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped AlgebraicCurve.Place

variable {k K L : Type} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The actual integral fiber's degree-zero Tate quotient is that of local integral units. -/
def integralFiberHerbrandH0Equiv (w : Place k L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    HerbrandH0 (L ≃ₐ[K] L) (fiberIntegralUnits (L := L) (w.restrict K)) ≃*
      HerbrandH0 (decompositionGroup (K := K) w) w.adicCompletionIntegers.units :=
  (herbrandH0EquivariantMulEquiv (integralFiberInducedEquiv (K := K) w)
    (integralFiberInducedEquiv_smul (K := K) w)).trans
      (inducedHerbrandH0EquivOfFiniteCyclic (decompositionGroup (K := K) w) σ hgen)

/-- The actual integral fiber's degree-minus-one Tate quotient is the local one. -/
def integralFiberHerbrandHMinusOneEquiv (w : Place k L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    HerbrandHMinusOne (L ≃ₐ[K] L) (fiberIntegralUnits (L := L) (w.restrict K)) σ ≃*
      HerbrandHMinusOne (decompositionGroup (K := K) w) w.adicCompletionIntegers.units
        (subgroupGeneratorOfGenerator (decompositionGroup (K := K) w) σ hgen) :=
  (herbrandHMinusOneEquivariantMulEquiv (integralFiberInducedEquiv (K := K) w)
    (integralFiberInducedEquiv_smul (K := K) w) σ).trans
      (inducedHerbrandHMinusOneEquivOfFiniteCyclic (decompositionGroup (K := K) w) σ hgen)

variable [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
    [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [IsCyclic (L ≃ₐ[K] L)]

/-- Every actual integral fiber block has finite Tate quotients and Herbrand quotient one. -/
theorem integralFiber_herbrandQuotient (v : Place k K) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    ∃ hF : HerbrandQuotientDefined (L ≃ₐ[K] L) (fiberIntegralUnits (L := L) v) σ,
      let _ : Finite (HerbrandH0 (L ≃ₐ[K] L) (fiberIntegralUnits (L := L) v)) := hF.1
      let _ : Finite (HerbrandHMinusOne (L ≃ₐ[K] L) (fiberIntegralUnits (L := L) v) σ) := hF.2
      herbrandQuotient (G := L ≃ₐ[K] L) (A := fiberIntegralUnits (L := L) v) σ = 1 := by
  obtain ⟨w, rfl⟩ := Place.exists_restrict_eq (M := L) v
  let δ := subgroupGeneratorOfGenerator (decompositionGroup (K := K) w) σ hgen
  have hδ := subgroupGeneratorOfGenerator_generates (decompositionGroup (K := K) w) σ hgen
  obtain ⟨hU, hvalue⟩ := decomposition_integralUnits_herbrandQuotient w δ hδ
  have : Finite (HerbrandH0 (decompositionGroup (K := K) w)
      w.adicCompletionIntegers.units) := hU.1
  have : Finite (HerbrandHMinusOne (decompositionGroup (K := K) w)
      w.adicCompletionIntegers.units δ) := hU.2
  let e0 := integralFiberHerbrandH0Equiv w σ hgen
  let em := integralFiberHerbrandHMinusOneEquiv w σ hgen
  have hF : HerbrandQuotientDefined (L ≃ₐ[K] L)
      (fiberIntegralUnits (L := L) (w.restrict K)) σ :=
    ⟨Finite.of_equiv _ e0.symm.toEquiv, Finite.of_equiv _ em.symm.toEquiv⟩
  refine ⟨hF, ?_⟩
  intro hF0 hFm
  rw [herbrandQuotient_eq_card_ratio, Nat.card_congr e0.toEquiv, Nat.card_congr em.toEquiv]
  exact hvalue

/-- Outside ramification both low Tate groups of the integral fiber vanish. -/
theorem integralFiber_herbrand_subsingleton_of_ramificationIndex_eq_one
    (w : Place k L) (he : w.ramificationIndex K = 1)
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    Subsingleton (HerbrandH0 (L ≃ₐ[K] L) (fiberIntegralUnits (L := L) (w.restrict K))) ∧
      Subsingleton (HerbrandHMinusOne (L ≃ₐ[K] L)
        (fiberIntegralUnits (L := L) (w.restrict K)) σ) := by
  let δ := subgroupGeneratorOfGenerator (decompositionGroup (K := K) w) σ hgen
  have hδ := subgroupGeneratorOfGenerator_generates (decompositionGroup (K := K) w) σ hgen
  have : Subsingleton (HerbrandH0 (decompositionGroup (K := K) w)
      w.adicCompletionIntegers.units) :=
    decomposition_integralUnits_herbrandH0_subsingleton_of_ramificationIndex_eq_one w he δ hδ
  have : Subsingleton (HerbrandHMinusOne (decompositionGroup (K := K) w)
      w.adicCompletionIntegers.units δ) :=
    decompositionLocalUnits_herbrandHMinusOne_subsingleton_of_ramificationIndex_eq_one w he δ hδ
  exact ⟨(integralFiberHerbrandH0Equiv w σ hgen).injective.subsingleton,
    (integralFiberHerbrandHMinusOneEquiv w σ hgen).injective.subsingleton⟩

/-- Everywhere-integral ideles have defined Herbrand quotient one. -/
theorem integralIdeles_herbrandQuotient (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    ∃ hU : HerbrandQuotientDefined (L ≃ₐ[K] L) (integralSubgroup (k := k) (K := L)) σ,
      let _ : Finite (HerbrandH0 (L ≃ₐ[K] L) (integralSubgroup (k := k) (K := L))) := hU.1
      let _ : Finite (HerbrandHMinusOne (L ≃ₐ[K] L)
        (integralSubgroup (k := k) (K := L)) σ) := hU.2
      herbrandQuotient (G := L ≃ₐ[K] L)
        (A := integralSubgroup (k := k) (K := L)) σ = 1 := by
  let B : Place k K → Type := fun v => fiberIntegralUnits (L := L) v
  let hAction : MulDistribMulAction (L ≃ₐ[K] L) (∀ v, B v) :=
    piMulDistribMulAction (L ≃ₐ[K] L) B
  let : SMul (L ≃ₐ[K] L) (∀ v, B v) := hAction.toMulAction.toSMul
  choose hF hQ using fun v : Place k K => integralFiber_herbrandQuotient v σ hgen
  have : ∀ v, Finite (HerbrandH0 (L ≃ₐ[K] L) (B v)) := fun v => (hF v).1
  have : ∀ v, Finite (HerbrandHMinusOne (L ≃ₐ[K] L) (B v) σ) := fun v => (hF v).2
  obtain ⟨S, hS⟩ := exists_finset_forall_restrict_not_mem_ramificationIndex_eq_one_of_isSeparable
    (K := k) (F := K) (F' := L)
  have haway : ∀ v, v ∉ S →
      Subsingleton (HerbrandH0 (L ≃ₐ[K] L) (B v)) ∧
        Subsingleton (HerbrandHMinusOne (L ≃ₐ[K] L) (B v) σ) := by
    intro v hv
    obtain ⟨w, rfl⟩ := Place.exists_restrict_eq (M := L) v
    exact integralFiber_herbrand_subsingleton_of_ramificationIndex_eq_one w (hS w hv) σ hgen
  obtain ⟨hP, hPvalue⟩ := herbrandQuotient_pi_eq_one_of_subsingleton_off_finset B S σ
    (fun v hv => (haway v hv).1) (fun v hv => (haway v hv).2) (fun v => hQ v.val)
  have : Finite (HerbrandH0 (L ≃ₐ[K] L) (∀ v, B v)) := hP.1
  have : Finite (HerbrandHMinusOne (L ≃ₐ[K] L) (∀ v, B v) σ) := hP.2
  let e : integralSubgroup (k := k) (K := L) ≃* (∀ v, B v) :=
    integralGroupByPlace (k := k) (K := K) (L := L)
  have he : ∀ (τ : L ≃ₐ[K] L) (a : integralSubgroup (k := k) (K := L)),
      e (τ • a) = τ • e a := fun τ a =>
    funext (integralGroupByPlace_smul (K := K) τ a)
  have hU : HerbrandQuotientDefined (L ≃ₐ[K] L)
      (integralSubgroup (k := k) (K := L)) σ :=
    ⟨Finite.of_equiv _ (herbrandH0EquivariantMulEquiv e he).symm.toEquiv,
      Finite.of_equiv _ (herbrandHMinusOneEquivariantMulEquiv e he σ).symm.toEquiv⟩
  refine ⟨hU, ?_⟩
  intro hU0 hUm
  exact (herbrandQuotient_eq_of_equivariantMulEquiv e he σ).trans hPvalue

end FunctionField.IdeleGroup

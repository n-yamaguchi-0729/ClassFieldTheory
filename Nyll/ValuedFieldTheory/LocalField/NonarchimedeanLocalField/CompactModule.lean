/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Compact modules over open scalar subrings

A compact submodule of a finite-dimensional vector space is finite over an open
Noetherian scalar subring. A scalar multiple of a basis lattice contains the
compact set; the Noetherian property then supplies finite generation.
-/

open scoped Pointwise
open Topology

namespace LocalFieldTheory

theorem moduleFinite_of_isCompact_of_isOpen
    {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [AddCommGroup E] [Module K E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul K E] [T2Space E]
    [FiniteDimensional K E] (A : Subring K) [IsNoetherianRing A]
    [moduleAE : Module A E] [towerAKE : IsScalarTower A K E]
    (S : Submodule A E) (hA : IsOpen (A : Set K))
    (hS : IsCompact (S : Set E)) : Module.Finite A S := by
  classical
  let b := Module.finBasis K E
  let U : Set E := ⋂ i, {y | b.equivFunL y i ∈ A}
  have hU : IsOpen U :=
    isOpen_iInter_of_finite fun i =>
      hA.preimage ((continuous_apply i).comp b.equivFunL.continuous)
  have hzero : (0 : E) ∈ U := by
    apply Set.mem_iInter.mpr
    intro i
    change b.equivFunL 0 i ∈ A
    rw [map_zero]
    exact A.zero_mem
  obtain ⟨r, hr⟩ := absorbs_iff_norm.mp
    (hS.isVonNBounded K (hU.mem_nhds hzero))
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm K r
  let N : Submodule A E := Submodule.span A (Set.range fun i => c • b i)
  have hN : IsNoetherian A N :=
    isNoetherian_span_of_finite A (Set.finite_range fun i => c • b i)
  have hSN : S ≤ N := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hr c hc.le hx
    have hy' : ∀ i, b.equivFunL y i ∈ A := Set.mem_iInter.mp hy
    change c • y ∈ N
    rw [← b.sum_repr y, Finset.smul_sum]
    apply Submodule.sum_mem
    intro i _
    have hi : c • b i ∈ N := Submodule.subset_span ⟨i, rfl⟩
    have hs := N.smul_mem (⟨b.repr y i, hy' i⟩ : A) hi
    rw [← IsScalarTower.algebraMap_smul K] at hs
    change (b.repr y i) • (c • b i) ∈ N at hs
    rwa [smul_comm] at hs
  have : IsNoetherian A S := isNoetherian_of_le hSN
  exact Module.IsNoetherian.finite A S

end LocalFieldTheory

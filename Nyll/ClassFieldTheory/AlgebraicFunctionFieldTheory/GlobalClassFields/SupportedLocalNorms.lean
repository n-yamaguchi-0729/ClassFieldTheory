/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SIdeles
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.ClassHerbrand
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormOpen

/-!
# Triviality from supported actual local norms

S-ideles representing every class turn local splitting at S and unramified
local norms outside S into a surjective class norm. The first norm inequality
then forces an actual finite cyclic extension to have degree one.
-/

noncomputable section
open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField

variable {k K : Type} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K]

/-- Actual supported local norm preimages force a cyclic extension to be trivial. -/
theorem finrank_eq_one_of_supported_local_norms
    {M : Type} [Field M] [Algebra k M] [Algebra K M] [IsScalarTower k K M]
    [FiniteDimensional K M] [IsGalois K M] [IsCyclic Gal(M/K)]
    [HasPrincipalDivisors k M]
    [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M] [FunctionField k M]
    (S : Finset (Place k K))
    (hS : Function.Surjective (IdeleGroup.sIdeleClass S))
    (hAway : ∀ w : Place k M, w.restrict K ∉ S → w.ramificationIndex K = 1)
    (hSplit : ∀ v : Place k K, v ∈ S → ∀ w : Place k M, ∀ hw : w.restrict K = v,
      Function.Surjective (IdeleGroup.localNormOver v w hw)) :
    Module.finrank K M = 1 := by
  have hNormTop : (IdeleClassGroup.norm (k := k) (K := K) (L := M)).range = ⊤ := by
    apply top_unique
    intro c _
    obtain ⟨a, rfl⟩ := hS c
    choose w hw using (fun v : Place k K => Place.exists_restrict_eq (M := M) v)
    have hpre (v : Place k K) : ∃ z : IdeleGroup k M,
        IdeleGroup.normComponent (k := k) (K := K) (L := M) v z = a.val v ∧
        (v ∉ S → IdeleGroup.fiberProjection (L := M) v z ∈
          IdeleGroup.fiberIntegralUnits (L := M) v) := by
      by_cases hv : v ∈ S
      · obtain ⟨x, hx⟩ := hSplit v hv (w v) (hw v) (a.val v)
        refine ⟨IdeleGroup.placeIdele (w v) x,
          (IdeleGroup.normComponent_placeIdele v (w v) (hw v) x).trans hx, ?_⟩
        exact fun hnot => (hnot hv).elim
      · have he : (w v).ramificationIndex K = 1 := hAway (w v) (by rw [hw v]; exact hv)
        obtain ⟨x, hxint, hx⟩ :=
          IdeleGroup.exists_integral_localNormOver_eq_of_ramificationIndex_eq_one
            v (w v) (hw v) he (a.val v) (a.property v hv)
        refine ⟨IdeleGroup.placeIdele (w v) x,
          (IdeleGroup.normComponent_placeIdele v (w v) (hw v) x).trans hx, ?_⟩
        exact fun _ => IdeleGroup.fiberProjection_placeIdele_mem_integral v (w v) x hxint
    choose z hz hzi using hpre
    have hnorm : a.val ∈ (IdeleGroup.norm (k := k) (K := K) (L := M)).range := by
      apply IdeleGroup.mem_norm_range_of_normComponent_preimages a.val z hz
      have hnot : ∀ᶠ v : Place k K in Filter.cofinite, v ∉ S :=
        S.finite_toSet.compl_mem_cofinite
      exact hnot.mono fun v hv => hzi v hv
    obtain ⟨z, hz⟩ := hnorm
    exact ⟨IdeleClassGroup.mk (k := k) (K := M) z,
      congrArg (IdeleClassGroup.mk (k := k) (K := K)) hz⟩
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(M/K))
  have hlower := IdeleClassGroup.finrank_le_card_normQuotient (k := k) σ hσ
  change Module.finrank K M ≤
    (IdeleClassGroup.norm (k := k) (K := K) (L := M)).range.index at hlower
  rw [hNormTop, Subgroup.index_top] at hlower
  exact le_antisymm hlower Module.finrank_pos

end FunctionField

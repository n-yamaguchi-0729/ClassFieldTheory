/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.Norm
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormPreimage
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.ClassGroupNorm

/-!
# Norms of ideles supported at one place

The global norm of a one-place idele is the one-place idele of its actual
completed field norm. Thus local norms give genuine global class norms.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

namespace IdeleGroup

/-- The norm of a one-place idele is supported at the restricted place. -/
@[simp]
theorem norm_placeIdele (w : Place k L) (x : w.adicCompletionˣ) :
    norm (K := K) (L := L) (placeIdele w x) =
      placeIdele (w.restrict K) (localNorm (K := K) w x) := by
  classical
  apply IdeleGroup.ext
  intro v
  by_cases hv : w.restrict K = v
  · subst v
    change normComponent (K := K) (L := L) (w.restrict K) (placeIdele w x) =
      component (w.restrict K) (placeIdele (w.restrict K) (localNorm (K := K) w x))
    rw [component_placeIdele_same]
    exact normComponent_placeIdele (w.restrict K) w rfl x
  · change normComponent (K := K) (L := L) v (placeIdele w x) =
      component v (placeIdele (w.restrict K) (localNorm (K := K) w x))
    rw [component_placeIdele_of_ne _ v _ (Ne.symm hv), normComponent_apply]
    apply Finset.prod_eq_one
    intro z _
    have hz : z.1 ≠ w := by
      intro h
      apply hv
      exact h ▸ (Place.mem_fiberOver v).mp z.2
    change localNormOver v z.1 _ (component z.1 (placeIdele w x)) = 1
    rw [component_placeIdele_of_ne w z.1 x hz, map_one]

end IdeleGroup

namespace IdeleClassGroup

variable [Algebra.IsSeparable K L] [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- Inserting an actual local norm gives an actual all-place class norm. -/
theorem placeIdele_mk_mem_norm_range (w : Place k L)
    (x : (w.restrict K).adicCompletionˣ)
    (hx : x ∈ (IdeleGroup.localNorm (K := K) w).range) :
    (QuotientGroup.mk (IdeleGroup.placeIdele (w.restrict K) x) : IdeleClassGroup k K) ∈
      (norm (k := k) (K := K) (L := L)).range := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨(QuotientGroup.mk (IdeleGroup.placeIdele w y) : IdeleClassGroup k L), ?_⟩
  rw [norm_mk, IdeleGroup.norm_placeIdele]

end IdeleClassGroup

end FunctionField

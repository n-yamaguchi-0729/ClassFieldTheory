/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.OrbitBlocks
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.Norm

/-!
# Assembling actual local norm preimages

The norm of an idele supported at one place contributes precisely its completed
field norm. Local fiber preimages that are integral almost everywhere assemble
to an actual all-place idele preimage through the concrete fiber regrouping.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place RestrictedProduct

namespace FunctionField.IdeleGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

/-- A single actual place contributes exactly its completed field norm to its base component. -/
theorem normComponent_placeIdele (v : Place k K) (w : Place k L)
    (hw : w.restrict K = v) (x : w.adicCompletionˣ) :
    normComponent (k := k) (K := K) (L := L) v (placeIdele w x) =
      localNormOver v w hw x := by
  classical
  let u : v.fiberOver L := ⟨w, (Place.mem_fiberOver v).mpr hw⟩
  rw [normComponent_apply, Finset.prod_eq_single u]
  · change localNormOver v w hw (component w (placeIdele w x)) = _
    rw [component_placeIdele_same]
  · intro z _ hzu
    have hne : z.1 ≠ w := fun h => hzu (Subtype.ext h)
    change localNormOver v z.1 _ (component z.1 (placeIdele w x)) = 1
    rw [component_placeIdele_of_ne w z.1 x hne, map_one]
  · exact fun h => (h (Finset.mem_univ u)).elim

/-- A single integral local unit gives an integral actual fiber block. -/
theorem fiberProjection_placeIdele_mem_integral (v : Place k K) (w : Place k L)
    (x : w.adicCompletionˣ) (hx : x ∈ w.adicCompletionIntegers.units) :
    fiberProjection (L := L) v (placeIdele w x) ∈ fiberIntegralUnits (L := L) v := by
  intro u
  change component u.1 (placeIdele w x) ∈ u.1.adicCompletionIntegers.units
  by_cases hu : u.1 = w
  · rw [hu, component_placeIdele_same]
    exact hx
  · rw [component_placeIdele_of_ne w u.1 x hu]
    exact Subgroup.one_mem _

variable [Algebra.IsSeparable K L]

/-- Actual local fiber preimages with almost everywhere integral components assemble
to an actual idele norm preimage. -/
theorem mem_norm_range_of_normComponent_preimages (a : IdeleGroup k K)
    (b : Place k K → IdeleGroup k L)
    (hb : ∀ v, normComponent (k := k) (K := K) (L := L) v (b v) = a v)
    (hint : ∀ᶠ v : Place k K in Filter.cofinite,
      fiberProjection (L := L) v (b v) ∈ fiberIntegralUnits (L := L) v) :
    a ∈ (norm (k := k) (K := K) (L := L)).range := by
  let c : FiberRestrictedProduct (k := k) (K := K) (L := L) :=
    ⟨fun v => fiberProjection (L := L) v (b v), hint⟩
  let y := (groupByPlace (k := k) (K := K) (L := L)).symm c
  have hy : groupByPlace (k := k) (K := K) (L := L) y = c :=
    (groupByPlace (k := k) (K := K) (L := L)).apply_symm_apply c
  refine ⟨y, ?_⟩
  apply IdeleGroup.ext
  intro v
  change normComponent (k := k) (K := K) (L := L) v y = a v
  rw [← hb v, normComponent_apply, normComponent_apply]
  apply Finset.prod_congr rfl
  intro u _
  congr 1
  exact congrArg
    (fun d : FiberRestrictedProduct (k := k) (K := K) (L := L) => d v u) hy

end FunctionField.IdeleGroup

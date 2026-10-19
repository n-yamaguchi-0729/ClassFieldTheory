/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Topology

/-!
# Continuous idele homomorphisms are determined at one place

The finite products of the actual local components converge to an idele in
its restricted-product topology. All partial products lie in one principal
chart, where convergence is coordinatewise. Thus equality on every local
inclusion determines any continuous homomorphism into a Hausdorff group.
-/

noncomputable section

open scoped RestrictedProduct

namespace FunctionField.IdeleGroup

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The finite products of the local components converge in the actual
restricted-product topology to the original idele. -/
theorem hasProd_placeIdele (a : IdeleGroup k K) :
    HasProd (fun v : AlgebraicCurve.Place k K => placeIdele v (a v)) a := by
  classical
  let S : Set (AlgebraicCurve.Place k K) :=
    {v | a v ∈ v.adicCompletionIntegers.units}
  have hS : Filter.cofinite ≤ Filter.principal S :=
    Filter.le_principal_iff.mpr a.2
  let b : Πʳ v : AlgebraicCurve.Place k K,
      [v.adicCompletionˣ, v.adicCompletionIntegers.units]_[Filter.principal S] :=
    ⟨a, Filter.eventually_principal.mpr (fun _ hv => hv)⟩
  let f : AlgebraicCurve.Place k K → Πʳ v : AlgebraicCurve.Place k K,
      [v.adicCompletionˣ, v.adicCompletionIntegers.units]_[Filter.principal S] :=
    fun v => ⟨Pi.mulSingle v (a v), Filter.eventually_principal.mpr (by
      intro w hw
      by_cases h : w = v
      · subst w
        rw [Pi.mulSingle_eq_same]
        exact hw
      · rw [Pi.mulSingle_eq_of_ne h]
        exact Subgroup.one_mem _)⟩
  have hcoe : Topology.IsInducing
      (RestrictedProduct.coeMonoidHom
        (B := fun v : AlgebraicCurve.Place k K => v.adicCompletionIntegers.units)
        (𝓕 := Filter.principal S)) :=
    (RestrictedProduct.isEmbedding_coe_of_principal
      (R := fun v : AlgebraicCurve.Place k K => v.adicCompletionˣ)
      (A := fun v : AlgebraicCurve.Place k K =>
        (v.adicCompletionIntegers.units : Set v.adicCompletionˣ))).isInducing
  have hb : HasProd f b := by
    apply (hcoe.hasProd_iff f b).mp
    apply Pi.hasProd.mpr
    intro w
    change HasProd (fun v => Pi.mulSingle v (a v) w) (a w)
    have hw := hasProd_single (f := fun v => Pi.mulSingle v (a v) w) w
      (fun v hv => Pi.mulSingle_eq_of_ne
        (M := fun u : AlgebraicCurve.Place k K => u.adicCompletionˣ)
        (i := v) (i' := w) (x := a v) (Ne.symm hv))
    simpa only [Pi.mulSingle_eq_same] using hw
  let j : (Πʳ v : AlgebraicCurve.Place k K,
      [v.adicCompletionˣ, v.adicCompletionIntegers.units]_[Filter.principal S]) →*
      IdeleGroup k K :=
    { toFun := RestrictedProduct.inclusion _ _ hS
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact hb.map j (RestrictedProduct.continuous_inclusion hS)

/-- A continuous idele homomorphism to a Hausdorff commutative monoid is
determined by its values on all actual one-place inclusions. -/
theorem continuousMonoidHom_ext_placeIdele
    {M : Type*} [CommMonoid M] [TopologicalSpace M] [T2Space M]
    (f g : IdeleGroup k K →ₜ* M)
    (h : ∀ (v : AlgebraicCurve.Place k K) (x : v.adicCompletionˣ),
      f (placeIdele v x) = g (placeIdele v x)) : f = g := by
  apply ContinuousMonoidHom.ext
  intro a
  have hf := (hasProd_placeIdele a).map f.toMonoidHom f.continuous
  have hg := (hasProd_placeIdele a).map g.toMonoidHom g.continuous
  exact hf.unique (hg.congr_fun (fun v => h v (a v)))

end FunctionField.IdeleGroup

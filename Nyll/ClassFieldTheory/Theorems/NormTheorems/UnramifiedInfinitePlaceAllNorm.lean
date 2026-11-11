/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Definitions.NormTheorems.IsNormAtInfinitePlace
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.InfinitePlaceTensorNorm
public import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances

/-!
# Norms at an unramified infinite place

For a finite abelian extension, the determinant norm from the whole
archimedean tensor algebra is surjective when the base place is
unramified in the extension.
-/

@[expose] public section

open scoped NumberField TensorProduct NumberField.LiesOver
open NumberField

noncomputable section

namespace ClassFieldTheory

universe u v

/-- Every nonzero base-field element is an archimedean tensor norm at an
unramified infinite place of a finite abelian extension. -/
theorem isNormAtInfinitePlace_of_unramified
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (v : InfinitePlace K) (hv : v.IsUnramifiedIn L) (x : Kˣ) :
    IsNormAtInfinitePlace K L v x := by
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (K := L) v
  have hunramified : w.IsUnramified K := by
    have h : v.IsUnramifiedIn L ↔ w.IsUnramified K := by
      rw [← hw, InfinitePlace.isUnramifiedIn_comap]
    exact h.mp hv
  let : w.1.LiesOver v.1 := ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
  have htop : infiniteTensorNormSubgroup (K := K) (L := L) v = ⊤ := by
    rw [infiniteTensorNormSubgroup_eq_localNormSubgroup (K := K) (L := L) v w hw]
    apply top_unique
    intro z _
    refine ⟨Units.map (algebraMap v.Completion w.Completion).toMonoidHom z, ?_⟩
    apply Units.ext
    change Algebra.norm v.Completion
      (algebraMap v.Completion w.Completion (z : v.Completion)) = (z : v.Completion)
    rw [Algebra.norm_algebraMap,
      InfinitePlace.IsUnramified.finrank_eq_one v hunramified, pow_one]
  let xv : v.Completionˣ := Units.map (algebraMap K v.Completion) x
  have hnorm : xv ∈ infiniteTensorNormSubgroup (K := K) (L := L) v := by
    rw [htop]
    trivial
  obtain ⟨y, hy⟩ := hnorm
  exact ⟨y, congrArg Units.val hy⟩

end ClassFieldTheory

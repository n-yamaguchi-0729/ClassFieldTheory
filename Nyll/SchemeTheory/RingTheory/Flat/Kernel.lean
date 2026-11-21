/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_Flat_ker_of_surjective_of_flat.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_TwoChartCech_Mumford_flat_K0.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.Flat.Equalizer
public import Nyll.SchemeTheory.RingTheory.Flat.TensorInjectivity

/-!
# Module Flat ker of surjective of flat
-/

/-! Flatness of the kernel of a surjection between flat modules. -/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.Module_Flat_ker_of_surjective_of_flat

universe u v w

open TensorProduct

theorem _root_.Module.Flat.ker_of_surjective_of_flat
    {R : Type u} [CommRing R] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Flat R M] [Module.Flat R N] (g : M →ₗ[R] N) (hg : Function.Surjective g) :
    Module.Flat R (LinearMap.ker g) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro Q' Q _ _ _ _ i hi
  have hι_Q' : Function.Injective ((LinearMap.ker g).subtype.lTensor Q') :=
    LinearMap.lTensor_injective_of_exact_of_flat g hg _ (LinearMap.ker g).subtype_injective
      (LinearMap.exact_subtype_ker_map g) Q'
  have hi_M : Function.Injective (i.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap i hi
  intro x y hxy
  apply hι_Q'
  apply hi_M
  calc (i.rTensor M) (((LinearMap.ker g).subtype.lTensor Q') x)
      = ((LinearMap.ker g).subtype.lTensor Q) ((i.rTensor (LinearMap.ker g)) x) := by
        rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
            LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
    _ = ((LinearMap.ker g).subtype.lTensor Q) ((i.rTensor (LinearMap.ker g)) y) := by rw [hxy]
    _ = (i.rTensor M) (((LinearMap.ker g).subtype.lTensor Q') y) := by
        rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
            LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

end AlgebraicCurves.Foundations.Algebra.Proofs.Module_Flat_ker_of_surjective_of_flat
end ProofImplementation

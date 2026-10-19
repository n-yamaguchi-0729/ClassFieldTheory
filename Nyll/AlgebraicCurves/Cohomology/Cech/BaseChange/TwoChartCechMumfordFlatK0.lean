/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_TwoChartCech_Mumford_flat_K0.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.Covers.MumfordTruncation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Equalizer
import Nyll.SchemeTheory.RingTheory.Flat.Product

/-!
Flatness of the enlarged kernel in the finite-presentation construction.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.TwoChartCech_Mumford_flat_K0

noncomputable section

open scoped TensorProduct

universe u v w

namespace TwoChartCech
open _root_.TwoChartCech
namespace Mumford
open _root_.TwoChartCech.Mumford
open _root_.TwoChartCech.Mumford
open _root_.TwoChartCech

variable {R : Type u} [CommRing R]

theorem flat_ker_of_surjective' {M : Type v} {N : Type w} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Flat R M] [Module.Flat R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Module.Flat R (LinearMap.ker f) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro Q' Q _ _ _ _ i hi
  have hι_Q' : Function.Injective ((LinearMap.ker f).subtype.lTensor Q') :=
    LinearMap.lTensor_injective_of_exact_of_flat f hf _ (LinearMap.ker f).subtype_injective
      (LinearMap.exact_subtype_ker_map f) Q'
  have hi_M : Function.Injective (i.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap i hi
  intro x y hxy
  apply hι_Q'
  apply hi_M
  calc (i.rTensor M) (((LinearMap.ker f).subtype.lTensor Q') x)
      = ((LinearMap.ker f).subtype.lTensor Q) ((i.rTensor (LinearMap.ker f)) x) := by
        rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
            LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
    _ = ((LinearMap.ker f).subtype.lTensor Q) ((i.rTensor (LinearMap.ker f)) y) := by rw [hxy]
    _ = (i.rTensor M) (((LinearMap.ker f).subtype.lTensor Q') y) := by
        rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
            LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

end TwoChartCech.Mumford

open _root_.AlgebraicCurves.Cohomology.Cech.Proofs in
open _root_.TwoChartCech.Mumford TwoChartCech_Mumford_flat_K0.TwoChartCech.Mumford in
theorem _root_.TwoChartCech.Mumford.flat_K0
    {R : Type u} [CommRing R]
    {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    Module.Flat R (TwoChartCech.Mumford.K0 d) :=
  haveI : Module.Flat R (C0 × (Fin (rank d) → R)) :=
    Module.Flat.prod (R := R) C0 (Fin (rank d) → R)
  flat_ker_of_surjective' (d.coprod (lift d)) (surjective_coprod d)

end
end AlgebraicCurves.Cohomology.Cech.Proofs.TwoChartCech_Mumford_flat_K0
end ProofImplementation

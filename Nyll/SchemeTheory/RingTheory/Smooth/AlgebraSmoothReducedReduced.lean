/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.Smooth.Basic
public import Nyll.SchemeTheory.Morphisms.SmoothReducedReduced

/-!
# Algebra Smooth is Reduced of is Reduced of is Noetherian Ring
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace Algebra_Smooth_isReduced_of_isReduced_of_isNoetherianRing

universe u

open CategoryTheory AlgebraicGeometry

theorem _root_.Algebra.Smooth.isReduced_of_isReduced_of_isNoetherianRing
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    [IsReduced R] [IsNoetherianRing R] : IsReduced S := by
  have hsm : AlgebraicGeometry.Smooth (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)]
    change (algebraMap R S).Smooth
    rw [RingHom.smooth_algebraMap]
    infer_instance
  have := AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))
  exact (affine_isReduced_iff (CommRingCat.of S)).mp this
end Algebra_Smooth_isReduced_of_isReduced_of_isNoetherianRing
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation

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

public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.IdealSheafModuleMaps
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.Cartier
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.IdealSheafDataPullbackModuleComparisonLocallySurjective
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Invertible.InvertibleIsoLocallySurjective
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealInvertibleModule

/-!
# Invertible ideal-module pullback comparisons

For invertible ideal sheaves on both schemes, the pullback module comparison
is an isomorphism.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison

universe u

open CategoryTheory AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison
  {X X' : Scheme.{u}} (f : X' ⟶ X) {I : X.IdealSheafData} (hI : I.IsInvertible)
    (hI' : (I.comap f).IsInvertible) : IsIso (I.pullbackModuleComparison f) :=
  Scheme.Modules.IsInvertible.isIso_of_locallySurjective
    (Scheme.Modules.IsInvertible.pullback f hI.isInvertible_module) hI'.isInvertible_module
    (I.pullbackModuleComparison f)
    (Scheme.IdealSheafData.pullbackModuleComparison_locallySurjective f I)
end Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

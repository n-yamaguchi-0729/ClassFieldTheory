/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_of_valuationSubring_of_isSeparable.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Nyll.AlgebraicCurves.Places.Basic
public import Nyll.AlgebraicCurves.Places.ValuationRings.BasicValuationSubringFiniteDimensional

/-!
# Place exists of valuation Subring of is Separable
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_exists_of_valuationSubring_of_isSeparable

open _root_.AlgebraicCurve
open _root_.IsDedekindDomain
open scoped IntermediateField.algebraAdjoinAdjoin

theorem _root_.AlgebraicCurve.Place.exists_of_valuationSubring_of_isSeparable
    {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]
    (A : ValuationSubring F) (hAK : ∀ a : K, algebraMap K F a ∈ A) (hA : A ≠ ⊤) :
    ∃ v : AlgebraicCurve.Place K F, v.toValuationSubring = A :=
  _root_.AlgebraicCurve.Place.exists_of_valuationSubring_of_finiteDimensional x A hAK hA

end AlgebraicCurves.Places.Proofs.Place_exists_of_valuationSubring_of_isSeparable
end ProofImplementation

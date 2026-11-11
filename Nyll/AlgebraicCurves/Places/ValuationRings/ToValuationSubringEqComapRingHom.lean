/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom.lean
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
# Place exists to Valuation Subring eq comap ring Hom
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_exists_toValuationSubring_eq_comap_ringHom

open _root_.AlgebraicCurve
open _root_.IsDedekindDomain
open scoped IntermediateField.algebraAdjoinAdjoin

theorem _root_.AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom {K F F' : Type*}
  [Field K] [Field F] [Field F'] [Algebra K F] [CharZero K] (x : F) [FiniteDimensional
  (IntermediateField.adjoin K ({x} : Set F)) F] (φ : F →+* F') (w : ValuationSubring F') (hwK : ∀
  a : K, φ (algebraMap K F a) ∈ w) (hwx : ∃ y : F, φ y ∉ w) : ∃ v : AlgebraicCurve.Place K F,
  v.toValuationSubring = w.comap φ := by
  refine _root_.AlgebraicCurve.Place.exists_of_valuationSubring_of_finiteDimensional
    x (w.comap φ) (fun a => hwK a) ?_
  intro h
  obtain ⟨y, hy⟩ := hwx
  exact hy (h ▸ ValuationSubring.mem_top y : y ∈ w.comap φ)

end AlgebraicCurves.Places.Proofs.Place_exists_toValuationSubring_eq_comap_ringHom
end ProofImplementation

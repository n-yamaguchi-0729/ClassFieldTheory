/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Completion
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.ValuedFieldTheory.Valuation.Completion.WeakApproximation
import Mathlib.Topology.Algebra.IsOpenUnits

/-!
# Weak approximation at finitely many places

Distinct places give inequivalent discrete valuations because their valuation
subrings differ. The existing weak approximation theorem therefore gives density
in the product of the actual completed fields used in the adele ring.
-/

open scoped WithZero

noncomputable section

namespace FunctionField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Diagonal elements approximate prescribed values at any finite family of
distinct places, including places at infinity. -/
theorem denseRange_pi_placeCompletion {ι : Type*} [Finite ι]
    (v : ι → AlgebraicCurve.Place k K) (hv : Function.Injective v) :
    DenseRange (fun x : K => fun i => algebraMap K (v i).adicCompletion x) := by
  let D : ι → ValuationTheory.DiscreteValuationField.DVF K :=
    fun i => { ValueGroup := ℤᵐ⁰, valuation := (v i).adicValuation }
  have hD : Pairwise (fun i j => ¬ (D i).valuation.IsEquiv (D j).valuation) := by
    intro i j hij heq
    apply hij
    apply hv
    apply AlgebraicCurve.Place.toValuationSubring_injective
    have h := (Valuation.isEquiv_iff_valuationSubring _ _).mp heq
    change (v i).adicValuation.valuationSubring = (v j).adicValuation.valuationSubring at h
    rw [(v i).adicValuation_valuationSubring, (v j).adicValuation_valuationSubring] at h
    exact h
  let e (i : ι) : (D i).valuation.Completion ≃ᵤ (v i).adicCompletion :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformEquiv
      K (v i).heightOneSpectrum).symm
  have he : DenseRange (Pi.map (fun i => e i)) :=
    DenseRange.piMap fun i => (e i).surjective.denseRange
  have h := he.comp
    (ValuationTheory.DiscreteValuationField.DVF.denseRange_pi_completion D hD)
    (continuous_pi fun i => (e i).continuous.comp (continuous_apply i))
  exact h

/-- Nonzero diagonal elements approximate prescribed units at any finite family
of distinct completed places. -/
theorem denseRange_pi_placeCompletionUnits {ι : Type*} [Finite ι]
    (v : ι → AlgebraicCurve.Place k K) (hv : Function.Injective v) :
    DenseRange (fun x : Kˣ => fun i =>
      Units.map (algebraMap K (v i).adicCompletion).toMonoidHom x) := by
  classical
  by_cases hi : Nonempty ι
  · let i₀ : ι := Classical.choice hi
    let u : (∀ i, (v i).adicCompletionˣ) → ∀ i, (v i).adicCompletion :=
      Pi.map (fun _ => Units.val)
    have hu : Topology.IsOpenEmbedding u :=
      Topology.IsOpenEmbedding.piMap
        (fun i => IsOpenUnits.isOpenEmbedding_unitsVal (M := (v i).adicCompletion))
    apply dense_iff_inter_open.mpr
    intro U hU hne
    obtain ⟨a, ha⟩ := (denseRange_pi_placeCompletion v hv).exists_mem_open
      (hu.isOpenMap U hU) (hne.image u)
    obtain ⟨b, hb, hab⟩ := ha
    have ha0 : a ≠ 0 := by
      intro hz
      have h := congrFun hab i₀
      have hz' : (b i₀ : (v i₀).adicCompletion) = 0 := by
        simpa only [u, Pi.map_apply, hz, map_zero] using h
      exact (b i₀).ne_zero hz'
    let a' : Kˣ := Units.mk0 a ha0
    refine ⟨b, hb, a', ?_⟩
    funext i
    apply Units.ext
    exact (congrFun hab i).symm
  · have : IsEmpty ι := not_nonempty_iff.mp hi
    exact (show Function.Surjective
      (fun x : Kˣ => fun i => Units.map (algebraMap K (v i).adicCompletion).toMonoidHom x) from
        fun y => ⟨1, funext (fun i => isEmptyElim i)⟩).denseRange

end FunctionField

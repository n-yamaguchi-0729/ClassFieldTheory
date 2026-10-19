/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

The separating-parameter scalar transfer is supplied by
Nyll/AlgebraicCurves/FunctionFields/Rational/SeparatingRationalPresentation.lean,
extracted from the following source, originally Copyright 2026 Anthropic, PBC, Apache 2.0:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver.lean
Upstream NOTICE:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Adele.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Constants
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.RiemannRoch
import Nyll.AlgebraicCurves.Places.Completion
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.FiniteDimensionalLSpaceZero
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Index.AdicValuationSubLeRiemannGenus
import Mathlib.Tactic.Choose
import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!
# Strong approximation for completed function-field adeles

The existing Riemann--Roch approximation theorem concerns repartitions with values in the
function field. Here density in each actual completion supplies a repartition approximating
a completed adele. Its exceptional places are finite, so the existing theorem applies away
from one place. A final ultrametric estimate gives the requested completed precision.

Neither a genus witness nor separability of the chosen rational presentation is an input.
Perfectness supplies a separating parameter, and the existing index-of-specialty theorem
supplies the genus witness. The base field need not be the full field of constants.
-/

noncomputable section

open AlgebraicCurve
open scoped RestrictedProduct WithZero

namespace FunctionField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

private theorem exists_completion_approx (v : Place k K) (a : v.adicCompletion) (n : ℤ) :
    ∃ f : K, Valued.v (a - algebraMap K v.adicCompletion f) ≤ WithZero.exp n := by
  obtain ⟨b, hb⟩ := v.heightOneSpectrum.valuedAdicCompletion_surjective K (WithZero.exp n)
  have hopen : IsOpen {y : v.adicCompletion | (y - a) / b ∈ v.adicCompletionIntegers} :=
    (Valued.isOpen_valuationSubring v.adicCompletion).preimage
      ((continuous_id.sub continuous_const).div_const b)
  have ha : a ∈ {y : v.adicCompletion | (y - a) / b ∈ v.adicCompletionIntegers} := by
    change (a - a) / b ∈ v.adicCompletionIntegers
    rw [sub_self, zero_div]
    exact zero_mem _
  have hdense : DenseRange (algebraMap K v.adicCompletion) :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap K v.heightOneSpectrum
  obtain ⟨f, hf⟩ := hdense.exists_mem_open hopen ⟨a, ha⟩
  change Valued.v ((algebraMap K v.adicCompletion f - a) / b) ≤ 1 at hf
  rw [map_div₀, hb] at hf
  have hpos : 0 < (WithZero.exp n : ℤᵐ⁰) :=
    pos_iff_ne_zero.mpr WithZero.exp_ne_zero
  refine ⟨f, ?_⟩
  rw [Valuation.map_sub_swap]
  exact (div_le_one₀ hpos).mp hf


namespace AdeleRing

variable [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [PerfectField k]

/-- Approximate an actual completed adele at every place other than `v₀`, with the
simultaneous precision specified by a divisor. -/
theorem exists_sub_le_away (a : AdeleRing k K) (D : Divisor k K) (v₀ : Place k K) :
    ∃ f : K, ∀ v : Place k K, v ≠ v₀ →
      Valued.v (a v - algebraMap K v.adicCompletion f) ≤ WithZero.exp (D v) := by
  classical
  have : IsCurveOver k K := isCurveOver k K
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Nonempty (Place k K) := ⟨v₀⟩
  have : FiniteDimensional k (LSpace (0 : Divisor k K)) :=
    finiteDimensional_lSpace_zero k K
  obtain ⟨γ, D₀, hreach⟩ := exists_genusReached (k := k) (K := K)
  choose α hα using fun v : Place k K => exists_completion_approx v (a v) (D v)
  have hD : ∀ᶠ v : Place k K in Filter.cofinite, D v = 0 :=
    D.support.eventually_cofinite_notMem.mono fun v hv => Finsupp.notMem_support_iff.mp hv
  have hgood : ∀ᶠ v : Place k K in Filter.cofinite,
      v.adicValuation (α v) ≤ WithZero.exp (D v) := by
    apply (a.2.and hD).mono
    intro v hv
    have hav : Valued.v (a v) ≤ 1 := hv.1
    have herror : Valued.v (a v - algebraMap K v.adicCompletion (α v)) ≤ 1 := by
      simpa only [hv.2, WithZero.exp_zero] using hα v
    have hmap : Valued.v (algebraMap K v.adicCompletion (α v)) ≤ 1 := by
      calc
        Valued.v (algebraMap K v.adicCompletion (α v)) =
            Valued.v (a v - (a v - algebraMap K v.adicCompletion (α v))) := by
          rw [sub_sub_cancel]
        _ ≤ 1 := Valued.v.map_sub_le hav herror
    rw [hv.2, WithZero.exp_zero]
    exact (valued_algebraMap_adicCompletion v (α v)) ▸ hmap
  have hbad : {v : Place k K | ¬ v.adicValuation (α v) ≤ WithZero.exp (D v)}.Finite :=
    Filter.eventually_cofinite.mp hgood
  have hbadAway :
      {v : Place k K | v ≠ v₀ ∧ ¬ v.adicValuation (α v) ≤ WithZero.exp (D v)}.Finite :=
    hbad.subset fun _ hv => hv.2
  obtain ⟨f, hf⟩ := exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt
    hreach {v : Place k K | v ≠ v₀} (fun h => h rfl) D α hbadAway
  refine ⟨f, fun v hv => ?_⟩
  have hlocal : Valued.v (algebraMap K v.adicCompletion (α v - f)) ≤
      WithZero.exp (D v) := by
    rw [valued_algebraMap_adicCompletion]
    exact hf v hv
  calc
    Valued.v (a v - algebraMap K v.adicCompletion f) =
        Valued.v ((a v - algebraMap K v.adicCompletion (α v)) +
          algebraMap K v.adicCompletion (α v - f)) := by
      rw [map_sub (algebraMap K v.adicCompletion), sub_add_sub_cancel]
    _ ≤ WithZero.exp (D v) := Valued.v.map_add_le (hα v) hlocal

/-- Finite prescribed completed values and precision can be met by a single field element,
which is integral at every other place except the one allowed pole `v₀`. -/
theorem exists_approx_integral_away (S : Finset (Place k K))
    (x : ∀ v : Place k K, v.adicCompletion) (n : Place k K → ℤ)
    (v₀ : Place k K) (hv₀ : v₀ ∉ S) :
    ∃ f : K,
      (∀ v ∈ S, Valued.v (x v - algebraMap K v.adicCompletion f) ≤ WithZero.exp (n v)) ∧
      (∀ v : Place k K, v ∉ S → v ≠ v₀ →
        algebraMap K v.adicCompletion f ∈ v.adicCompletionIntegers) := by
  classical
  let a : AdeleRing k K :=
    ⟨fun v => if v ∈ S then x v else 0,
      S.eventually_cofinite_notMem.mono fun v hv => by
        change (if v ∈ S then x v else 0) ∈ v.adicCompletionIntegers
        rw [ite_eq_right hv]
        exact zero_mem _⟩
  let D : Divisor k K := ∑ v ∈ S, Finsupp.single v (n v)
  have ha_apply (v : Place k K) : a v = if v ∈ S then x v else 0 := rfl
  have hD : ∀ v : Place k K, D v = if v ∈ S then n v else 0 := by
    intro v
    simp only [D, Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq']
  obtain ⟨f, hf⟩ := exists_sub_le_away a D v₀
  refine ⟨f, ?_, ?_⟩
  · intro v hv
    have hne : v ≠ v₀ := fun h => hv₀ (h ▸ hv)
    have h := hf v hne
    simpa only [ha_apply, hD, ite_eq_left hv] using h
  · intro v hv hne
    have h := hf v hne
    change Valued.v (algebraMap K v.adicCompletion f) ≤ 1
    simpa only [ha_apply, hD, ite_eq_right hv, zero_sub, Valuation.map_neg,
      WithZero.exp_zero] using h

end AdeleRing

end FunctionField

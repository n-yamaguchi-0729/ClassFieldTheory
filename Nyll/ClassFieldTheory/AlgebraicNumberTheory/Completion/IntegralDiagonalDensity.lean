/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.Valuation.Completion.AdicCompletion
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.Comparison
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.ExtensionIndex

/-! # Simultaneous density of the integral diagonal in adic completions -/

@[expose] public section

open scoped WithZero NumberField
open IsDedekindDomain Valuation.IsRankOneDiscrete

namespace IsDedekindDomain.HeightOneSpectrum

variable {A K ι : Type*} [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]

/-- The diagonal of a Dedekind domain is dense in the product of the rings of
integers of its adic completions at any family of distinct height-one primes. -/
theorem denseRange_integerAlgebraMap_pi
    (p : ι → HeightOneSpectrum A) (hp : Function.Injective p) :
    DenseRange fun (a : A) i => algebraMap A ((p i).adicCompletionIntegers K) a := by
  classical
  intro x
  apply mem_closure_iff.mpr
  intro U hU hx
  have hUnhds := hU.mem_nhds hx
  rw [nhds_pi, Filter.mem_pi'] at hUnhds
  obtain ⟨s, V, hV, hsub⟩ := hUnhds
  have hball (i : ι) : ∃ e : ℤᵐ⁰ˣ,
      ∀ a : A, Valued.v ((algebraMap A K a) - (x i : (p i).adicCompletion K)) < e.val →
        algebraMap A ((p i).adicCompletionIntegers K) a ∈ V i := by
    let v := (Valued.v : Valuation ((p i).adicCompletion K) ℤᵐ⁰)
    obtain ⟨T, hT, hTV⟩ := (mem_nhds_subtype _ _ _).mp (hV i)
    obtain ⟨γ, hγ⟩ := (Valued.mem_nhds (Γ₀ := ℤᵐ⁰)).mp hT
    let e := Units.mapEquiv (valueGroup₀_equiv_withZeroMulInt v).toMulEquiv γ
    refine ⟨e, fun a ha => hTV (hγ ?_)⟩
    apply (valueGroup₀_equiv_withZeroMulInt_strictMono v).lt_iff_lt.mp
    rw [valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
      (valuedAdicCompletion_surjective K (p i))]
    exact ha
  choose e he using hball
  obtain ⟨a, ha⟩ := exists_forall_adicValued_sub_lt K s e p hp x
  exact ⟨fun i => algebraMap A ((p i).adicCompletionIntegers K) a,
    hsub (fun i hi => he i a (ha i hi)), ⟨a, rfl⟩⟩

/-- The original prime extends to the maximal ideal with exponent one in
its adic completion. The integer uniformizer maps to a local uniformizer. -/
theorem map_asIdeal_adicCompletionIntegers (p : HeightOneSpectrum A) :
    p.asIdeal.map (algebraMap A (p.adicCompletionIntegers K)) = p.completionIdeal K := by
  let j := algebraMap A (p.adicCompletionIntegers K)
  have hcomap : (p.completionIdeal K).comap j = p.asIdeal :=
    (Ideal.over_def (p.completionIdeal K) p.asIdeal).symm
  apply le_antisymm
  · exact Ideal.map_le_iff_le_comap.mpr hcomap.symm.le
  · obtain ⟨a, ha⟩ := p.intValuation_exists_uniformizer
    have ha' : Valued.v (j a : p.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ) := by
      rw [← WithZero.exp, ← ha, ← ValuationSubring.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply, p.valuedAdicCompletion_eq_valuation,
        p.valuation_of_algebraMap]
    have hmem : a ∈ p.asIdeal := by
      rw [← hcomap, Ideal.mem_comap, mem_completionIdeal_iff, ha']
      change WithZero.exp (-1 : ℤ) < 1
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      exact neg_one_lt_zero
    change IsLocalRing.maximalIdeal (p.adicCompletionIntegers K) ≤ p.asIdeal.map j
    rw [adicCompletion.maximalIdeal_eq_span_uniformizer K p ha', Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem j hmem

end IsDedekindDomain.HeightOneSpectrum

open NumberField AlgebraicNumberTheory.Valuations

namespace AlgebraicNumberTheory.Valuations

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

/-- The integral diagonal in the exact absolute-value completions above a
finite place. -/
def finitePlaceIntegralDiagonal (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 L)
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv K v) L) :
    absoluteValueCompletionIntegers w.1
      (absoluteValueExtension_isNonarchimedean (HeightOneSpectrum.adicAbv K v)
        (HeightOneSpectrum.isNonarchimedean_adicAbv K v) w) :=
  ⟨AbsoluteValue.toCompletion w.1 (a : L),
    (finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff v w _).mp (by
      rw [finitePlaceExtensionAdicCompletionRingEquiv_toCompletion]
      exact (algebraMap (𝓞 L) ((finitePlaceExtensionCentre v w).adicCompletionIntegers L) a).2)⟩

/-- The integral diagonal is dense in the actual product of valuation
rings indexed by the finite extensions of the base place. -/
theorem denseRange_finitePlaceIntegralDiagonal (v : HeightOneSpectrum (𝓞 K)) :
    DenseRange (finitePlaceIntegralDiagonal (L := L) v) := by
  let vK := HeightOneSpectrum.adicAbv K v
  let W := AbsoluteValueExtension vK L
  let p : W → HeightOneSpectrum (𝓞 L) := fun w => finitePlaceExtensionCentre v w
  have hp : Function.Injective p := by
    intro w z h
    exact (finitePlaceExtensionEquivAbove (L := L) v).injective (Subtype.ext h)
  let V (w : W) := absoluteValueCompletionIntegers w.1
    (absoluteValueExtension_isNonarchimedean vK (HeightOneSpectrum.isNonarchimedean_adicAbv K v) w)
  let e (w : W) := finitePlaceExtensionAdicCompletionRingEquiv v w
  let f (w : W) (x : (p w).adicCompletionIntegers L) : V w :=
    ⟨(e w).symm (x : (p w).adicCompletion L),
      (finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff v w _).mp (by
        change e w ((e w).symm _) ∈ _
        rw [RingEquiv.apply_symm_apply]
        exact x.2)⟩
  have hf (w : W) : Continuous (f w) := by
    have he₁ : Continuous (finitePlaceExtensionCompletionRingEquiv v w).symm := by
      have h := (AbsoluteValue.Completion.continuous_ofCompletion w.1).comp
        ((show Continuous (UniformSpace.Completion.map
          (finitePlaceExtensionWithAbsRingEquiv v w).symm) from
            UniformSpace.Completion.continuous_map).comp
          (AbsoluteValue.Completion.continuous_toCompletion
            (HeightOneSpectrum.adicAbv L (finitePlaceExtensionCentre v w))))
      refine h.congr fun x => ?_
      simp only [Function.comp_apply, finitePlaceExtensionCompletionRingEquiv,
        RingEquiv.symm_trans_apply, RingEquiv.symm_symm, AbsoluteValue.Completion.equiv_apply,
        AbsoluteValue.Completion.equiv_symm_apply, UniformSpace.Completion.mapRingEquiv_symm_apply]
    have he₂ : Continuous (finitePlaceCompletionRingEquiv (p w)).symm :=
      (finitePlaceCompletionContinuousMulEquiv (p w)).symm.continuous
    exact ((he₁.comp he₂).comp continuous_subtype_val).subtype_mk _
  let g (x : ∀ w : W, (p w).adicCompletionIntegers L) : ∀ w, V w := fun w => f w (x w)
  have hg : Function.Surjective g := by
    intro y
    refine ⟨fun w => ⟨e w (y w), (finitePlaceExtensionAdicCompletionRingEquiv_mem_integers_iff
      v w _).mpr (y w).2⟩, ?_⟩
    funext w
    exact Subtype.ext ((e w).symm_apply_apply (y w : w.1.Completion))
  have h := hg.denseRange.comp
    (IsDedekindDomain.HeightOneSpectrum.denseRange_integerAlgebraMap_pi (K := L) p hp)
    (continuous_pi fun w => (hf w).comp (continuous_apply w))
  have hdiag : g ∘ (fun (a : 𝓞 L) w => algebraMap (𝓞 L) ((p w).adicCompletionIntegers L) a) =
      finitePlaceIntegralDiagonal (L := L) v := by
    funext a w
    apply Subtype.ext
    apply (e w).injective
    change e w ((e w).symm _) = e w (AbsoluteValue.toCompletion w.1 (a : L))
    rw [RingEquiv.apply_symm_apply]
    exact (finitePlaceExtensionAdicCompletionRingEquiv_toCompletion v w (a : L)).symm
  rwa [hdiag] at h

end

end AlgebraicNumberTheory.Valuations

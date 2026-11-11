/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_existsUnique_pDigits_of_transcendental.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.FunctionFields.FrobeniusSubfield
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.Relrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Algebra.CharP.Algebra

/-!
# Exists Unique p Digits of transcendental
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.ExistsUnique_pDigits_of_transcendental

noncomputable section

namespace AlgebraicCurve
namespace PthPowerIndex

open IntermediateField Polynomial

private def frobeniusSubfield (M : Type*) [Field M] (p : ℕ) [ExpChar M p] : Subfield M :=
  (frobenius M p).fieldRange

open _root_.AlgebraicCurve (frobeniusRingEquivRange frobeniusRingEquivRange_apply
  finrank_frobeniusSubfield_eq_of_transcendental pDigits_exists_of_finrank_eq)

private theorem pDigits_existsUnique_of_transcendental {K M : Type*} [Field K] [Field M]
    [Algebra K M] [PerfectField K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (t : M) (htr : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set M)) M]
    (htp : ∀ a : M, a ^ p ≠ t) (g : M) :
    ∃! a : Fin p → M, g = ∑ i : Fin p, a i ^ p * t ^ (i : ℕ) := by
  have : CharP M p := charP_of_injective_algebraMap (algebraMap K M).injective p
  have : ExpChar M p := ExpChar.prime hp.out
  have hlin :=
    _root_.AlgebraicCurve.linearIndependent_pow_over_frobenius p htp
  have hfr := finrank_frobeniusSubfield_eq_of_transcendental p t htr
  have hcard : Fintype.card (Fin p) = Module.finrank (frobeniusSubfield M p) M :=
    (Fintype.card_fin p).trans hfr.symm
  let b : Module.Basis (Fin p) (frobeniusSubfield M p) M :=
    basisOfLinearIndependentOfCardEqFinrank hlin hcard
  have hbapply : ∀ i : Fin p, (b i : M) = t ^ (i : ℕ) := fun i ↦
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hlin hcard) i
  have hexpand : ∀ (c : Fin p → M),
      ∑ i : Fin p, c i ^ p * t ^ (i : ℕ) =
        ∑ i : Fin p, (frobeniusRingEquivRange M p (c i) : frobeniusSubfield M p) • b i := by
    intro c
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hbapply i, Subfield.smul_def, frobeniusRingEquivRange_apply, smul_eq_mul]
  obtain ⟨a, ha⟩ := pDigits_exists_of_finrank_eq p hfr htp g
  refine ⟨a, ha, ?_⟩
  intro a' ha'
  have key : ∀ i, frobeniusRingEquivRange M p (a i) = frobeniusRingEquivRange M p (a' i) := by
    intro i
    have hga : g = ∑ j : Fin p, (frobeniusRingEquivRange M p (a j) :
        frobeniusSubfield M p) • b j := ha.trans (hexpand a)
    have hga' : g = ∑ j : Fin p, (frobeniusRingEquivRange M p (a' j) :
        frobeniusSubfield M p) • b j := ha'.trans (hexpand a')
    have hra := b.repr_sum_self
      (c := fun j ↦ (frobeniusRingEquivRange M p (a j) : frobeniusSubfield M p))
    have hra' := b.repr_sum_self
      (c := fun j ↦ (frobeniusRingEquivRange M p (a' j) : frobeniusSubfield M p))
    have hrepr := congrArg (fun x : M ↦ (b.repr x : Fin p → frobeniusSubfield M p))
      (hga.symm.trans hga')
    exact congrFun (hra.symm.trans (hrepr.trans hra')) i
  funext i
  exact (frobeniusRingEquivRange M p).injective (key i).symm

end AlgebraicCurve.PthPowerIndex

theorem _root_.AlgebraicCurve.existsUnique_pDigits_of_transcendental {K M : Type*} [Field K] [Field
  M] [Algebra K M]
    [PerfectField K] (p : ℕ) [hp : Fact p.Prime] [CharP K p] (t : M) (htr : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set M)) M] (htp : ∀ a : M, a ^ p ≠ t)
    (g : M) :
    ∃! a : Fin p → M, g = ∑ i : Fin p, a i ^ p * t ^ (i : ℕ) :=
  AlgebraicCurve.PthPowerIndex.pDigits_existsUnique_of_transcendental p t htr htp g

end
end AlgebraicCurves.Places.Proofs.ExistsUnique_pDigits_of_transcendental
end ProofImplementation

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_separating_transcendental_of_perfectField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.FunctionFields.Extensions.FiniteSimpleExtensions
public import Nyll.SchemeTheory.FunctionFields.FrobeniusSubfield
public import Nyll.SchemeTheory.FunctionFields.AlgebraIsSeparableFinrankFieldRangeFrobeniusEq

/-!
# Exists separating transcendental of perfect Field
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.Exists_separating_transcendental_of_perfectField

open IntermediateField

namespace AlgebraicCurve
namespace SeparatingTranscendentalOfPerfectField

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isTranscendenceBasis_of_transcendental {x : F} (hx : Transcendental K x)
    (hfd : FiniteDimensional K⟮x⟯ F) : IsTranscendenceBasis K (fun _ : Fin 1 => x) := by
  have hind : AlgebraicIndependent K (fun _ : Fin 1 => x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  refine hind.isTranscendenceBasis_iff_isAlgebraic.mpr ?_
  have hr : Set.range (fun _ : Fin 1 => x) = ({x} : Set F) := by
    ext y
    constructor
    · rintro ⟨_, rfl⟩
      exact Set.mem_singleton x
    · intro hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact ⟨0, rfl⟩
  rw [hr, ← IntermediateField.isAlgebraic_adjoin_iff_top]
  have := hfd
  exact Algebra.IsAlgebraic.of_finite K⟮x⟯ F

theorem isAlgebraic_adjoin_of_transcendental {x : F} (hx : Transcendental K x)
    (hfd : FiniteDimensional K⟮x⟯ F) {t : F} (ht : Transcendental K t) :
    Algebra.IsAlgebraic K⟮t⟯ F := by
  classical
  have htind : AlgebraicIndepOn K id ({t} : Set F) := by
    refine algebraicIndependent_unique_type_iff.mpr ?_
    simpa using ht
  obtain ⟨s, hts, hbasis⟩ := exists_isTranscendenceBasis_superset htind
  have hcard := hbasis.lift_cardinalMk_eq (isTranscendenceBasis_of_transcendental hx hfd)
  simp only [Cardinal.mk_fin, Nat.cast_one, Cardinal.lift_one, Cardinal.lift_eq_one] at hcard
  have hsub : s.Subsingleton := Cardinal.mk_le_one_iff_set_subsingleton.mp hcard.le
  have hseq : s = {t} := hsub.eq_singleton_of_mem (hts rfl)
  subst hseq
  have h := hbasis.isAlgebraic_field
  rwa [Subtype.range_coe] at h

theorem finiteDimensional_adjoin_of_transcendental {x : F} (_hx : Transcendental K x)
    (hfd : FiniteDimensional K⟮x⟯ F) {t : F} (ht : Transcendental K t) :
    FiniteDimensional K⟮t⟯ F := by
  clear _hx
  let : FiniteDimensional K⟮x⟯ F := hfd
  exact _root_.AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x ht

theorem transcendental_of_not_mem_fieldRange_frobenius [PerfectField K] (p : ℕ)
    [Fact p.Prime] [CharP K p] [CharP F p] {t : F} (ht : t ∉ (frobenius F p).fieldRange) :
    Transcendental K t := by
  intro halg
  apply ht
  have : Algebra.IsAlgebraic K K⟮t⟯ :=
    IntermediateField.isAlgebraic_adjoin_simple halg.isIntegral
  have : PerfectField K⟮t⟯ := Algebra.IsAlgebraic.perfectField (K := K)
  have : CharP K⟮t⟯ p := charP_of_injective_algebraMap (algebraMap K K⟮t⟯).injective p
  obtain ⟨s, hs⟩ := surjective_frobenius K⟮t⟯ p ⟨t, mem_adjoin_simple_self K t⟩
  refine RingHom.mem_fieldRange.mpr ⟨(s : F), ?_⟩
  have h := congrArg (fun u : K⟮t⟯ => (u : F)) hs
  simpa [frobenius_def] using h

theorem exists_separating [PerfectField K] {x : F} (hx : Transcendental K x)
    (hfd : FiniteDimensional K⟮x⟯ F) :
    ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F := by
  classical
  have := hfd
  obtain h0 | ⟨p, hp, hchar⟩ := CharP.exists' K
  · have : CharZero K⟮x⟯ := charZero_of_injective_algebraMap (algebraMap K K⟮x⟯).injective
    have : Algebra.IsAlgebraic K⟮x⟯ F := Algebra.IsAlgebraic.of_finite K⟮x⟯ F
    exact ⟨x, hx, hfd, Algebra.IsAlgebraic.isSeparable_of_perfectField⟩
  · have := hp
    have := hchar
    have : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
    have hdeg : Module.finrank (frobenius F p).fieldRange F = p :=
      AlgebraicCurve.finrank_frobeniusSubfield_eq_of_transcendental p x hx
    have hnle : ¬ ((⊤ : Subfield F) ≤ (frobenius F p).fieldRange) := by
      intro hle
      have h1 : Module.finrank (frobenius F p).fieldRange F = 1 := by
        rw [← Subfield.relfinrank_top_right, Subfield.relfinrank_eq_one_iff]
        exact hle
      exact hp.out.one_lt.ne (h1.symm.trans hdeg)
    obtain ⟨t, -, ht⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
    have httr : Transcendental K t := transcendental_of_not_mem_fieldRange_frobenius p ht
    have htfd : FiniteDimensional K⟮t⟯ F :=
      finiteDimensional_adjoin_of_transcendental hx hfd httr
    have := htfd
    have hsep : Algebra.IsSeparable K⟮t⟯ F :=
      Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq p hdeg
        (⟨t, mem_adjoin_simple_self K t⟩ : K⟮t⟯) ht
    exact ⟨t, httr, htfd, hsep⟩

end AlgebraicCurve.SeparatingTranscendentalOfPerfectField

theorem _root_.AlgebraicCurve.exists_separating_transcendental_of_perfectField
    {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ∃ t : F, Transcendental K t ∧
      FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F ∧
      Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F :=
  AlgebraicCurve.SeparatingTranscendentalOfPerfectField.exists_separating htr hfd
end AlgebraicCurves.FunctionFields.Proofs.Exists_separating_transcendental_of_perfectField
end ProofImplementation

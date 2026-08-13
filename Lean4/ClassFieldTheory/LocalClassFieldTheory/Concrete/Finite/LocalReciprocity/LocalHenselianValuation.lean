import LocalClassFieldTheory.Concrete.Finite.LocalReciprocity.AbstractFixedFieldNorm
import LocalClassFieldTheory.Concrete.Finite.LocalReciprocity.FiniteResidueFinrankTransfer
import LocalClassFieldTheory.Concrete.Finite.LocalReciprocity.FiniteExtensionClassFieldAxiom

namespace LocalClassFieldTheory

open ClassFormation LocalFieldTheory

/-!
# Finite local reciprocity: the normalized local valuation is Henselian

For a nonarchimedean local field, the normalized discrete valuation on the
base unit group satisfies the Henselian valuation condition.  The value group is the copy of
the ordinary integers in the profinite integers.  For every finite abstract
field, including a non-normal one, the image after the abstract norm is the
ordinary residue-degree multiple of that value group.
-/

noncomputable section

open scoped NNReal ValuativeRel
/-- **Finite local reciprocity.**  The normalized valuation of a nonarchimedean local
field, on the actual fixed coefficient group in its separable closure, is a
Henselian valuation relative to the residue Frobenius degree datum. -/
noncomputable def localHenselianValuation
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ValuationData (localResidueDatum K)
      (galoisAmbientUnitsRep K (SeparableClosure K)) := by
  refine
    { toAddMonoidHom := localBaseValuation K
      integers_mem := intToProCInteger_mem_localBaseValuation_range K
      canonical_value_quotient_bijective :=
        localCanonicalValueQuotientMap_bijective K
      norm_range := ?_ }
  intro F
  let H := F.field
  letI := F.finite
  let E := abstractFixedField K (SeparableClosure K) H
  letI : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional K (SeparableClosure K) H F.finite

  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : Valued K (ValuativeRel.ValueGroupWithZero K) := inferInstance
  letI : (Valued.v : Valuation K
      (ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField
      (L := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)
  letI : CompleteSpace K := inferInstance

  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField K E
  letI : NormedSpace K E := spectralNorm.normedSpace K E
  letI : CompleteSpace E := spectralNorm.completeSpace K E
  letI : LocallyCompactSpace E :=
    LocallyCompactSpace.of_finiteDimensional_of_complete K E
  letI : IsUltrametricDist E :=
    ⟨fun x y z => by
      change ‖x - z‖ ≤ max ‖x - y‖ ‖y - z‖
      rw [← sub_add_sub_cancel x y z]
      exact isNonarchimedean_spectralNorm
        (K := K) (L := E) (x - y) (y - z)⟩
  letI : Valued E ℝ≥0 := NormedField.toValued
  let vE : Valuation E ℝ≥0 := Valued.v
  letI : vE.IsNontrivial :=
    (inferInstance : (NormedField.valuation (K := E)).IsNontrivial)
  letI : ValuativeRel E := ValuativeRel.ofValuation vE
  letI : vE.Compatible := Valuation.Compatible.ofValuation vE
  letI : ValuativeRel.IsNontrivial E :=
    (ValuativeRel.isNontrivial_iff_isNontrivial vE).2 inferInstance
  letI : IsValuativeTopology E :=
    isValuativeTopology_of_valued_ofValuation E ℝ≥0
  letI : IsNonarchimedeanLocalField E :=
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

  letI : (ValuativeRel.valuation K).HasExtension
      (ValuativeRel.valuation E) := by
    apply Valuation.HasExtension.ofComapInteger
    ext x
    change ValuativeRel.valuation E (algebraMap K E x) ≤ 1 ↔
      ValuativeRel.valuation K x ≤ 1
    rw [← (ValuativeRel.valuation E).vle_one_iff, vE.vle_one_iff]
    change spectralNorm K E (algebraMap K E x) ≤ 1 ↔
      ValuativeRel.valuation K x ≤ 1
    rw [spectralNorm_extends]
    exact Valued.toNormedField.norm_le_one_iff

  letI : Algebra.IsIntegral 𝒪[K] 𝒪[E] := ⟨by
    intro y
    have hyv : vE (y : E) ≤ 1 := by
      apply (vE.vle_one_iff).1
      apply ((ValuativeRel.valuation E).vle_one_iff).2
      exact y.property
    have hynorm : ‖(y : E)‖ ≤ 1 := by
      have hynnnorm : ‖(y : E)‖₊ ≤ 1 := by
        simpa [vE, NormedField.valuation_apply] using hyv
      exact_mod_cast hynnnorm
    change spectralNorm K E (y : E) ≤ 1 at hynorm
    have hcoeffNorm :
        ∀ n : ℕ, ‖(minpoly K (y : E)).coeff n‖ ≤ 1 :=
      (spectralValue_le_one_iff
        (minpoly.monic (Algebra.IsIntegral.isIntegral (y : E)))).1
        (by simpa [spectralNorm] using hynorm)
    have hcoeff :
        (↑(minpoly K (y : E)).coeffs : Set K) ⊆
          (ValuativeRel.valuation K).integer := by
      intro c hc
      obtain ⟨n, _hn, rfl⟩ := Polynomial.mem_coeffs_iff.mp hc
      exact ((ValuativeRel.valuation K).mem_integer_iff _).2
        (Valued.toNormedField.norm_le_one_iff.mp (hcoeffNorm n))
    let p : Polynomial 𝒪[K] :=
      (minpoly K (y : E)).toSubring
        (ValuativeRel.valuation K).integer hcoeff
    refine ⟨p, ?_, ?_⟩
    · exact (Polynomial.monic_toSubring
        (minpoly K (y : E)) (ValuativeRel.valuation K).integer hcoeff).2
          (minpoly.monic (Algebra.IsIntegral.isIntegral (y : E)))
    · apply Subtype.ext
      have hmaproot :
          Polynomial.aeval (y : E)
            (p.map (algebraMap 𝒪[K] K)) = 0 := by
        dsimp only [p]
        rw [show algebraMap 𝒪[K] K =
          (ValuativeRel.valuation K).integer.subtype from rfl,
          Polynomial.map_toSubring]
        exact minpoly.aeval K (y : E)
      change (ValuativeRel.valuation E).integer.subtype
        (Polynomial.eval₂ (algebraMap 𝒪[K] 𝒪[E]) y p) = (0 : E)
      rw [Polynomial.hom_eval₂]
      change Polynomial.aeval (y : E) p = 0
      rwa [Polynomial.aeval_map_algebraMap K (y : E) p] at hmaproot⟩

  letI : Algebra.IsIntegral
      (ValuativeRel.valuation K).valuationSubring
      (ValuativeRel.valuation E).valuationSubring := by
    change Algebra.IsIntegral 𝒪[K] 𝒪[E]
    infer_instance
  let hIntegralClosure : IsIntegralClosure
      (ValuativeRel.valuation E).valuationSubring
      (ValuativeRel.valuation K).valuationSubring E :=
    ValuationTheory.DiscreteValuationField.Valuation.valuationSubring_isIntegralClosure_of_isIntegral
      (ValuativeRel.valuation K) (ValuativeRel.valuation E)
  letI : IsIntegralClosure 𝒪[E] 𝒪[K] E := by
    change IsIntegralClosure
      (ValuativeRel.valuation E).valuationSubring
      (ValuativeRel.valuation K).valuationSubring E
    exact hIntegralClosure

  rw [localResidueDatum_residueDegree_eq_residueFinrank K F]
  exact localBaseValuation_comp_normToBase_range_eq_residueFinrank K H

end
end LocalClassFieldTheory

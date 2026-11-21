/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.FiniteTensorInvariant

/-! # Range of the invariant on the finite tensor cohomology -/

@[expose] public section

open CategoryTheory AlgebraicNumberTheory.Valuations ContinuousCohomology
open IsDedekindDomain NumberField
open GlobalClassFieldTheory.Reciprocity LocalClassFieldTheory LocalFieldTheory
open scoped NumberField TensorProduct ValuativeRel

noncomputable section
namespace ClassFieldTheory.Brauer

section Evaluation

variable {K : Type} [Field K] [NumberField K]
  (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K))

/-- The invariant of a finite tensor class is the invariant of its completed Brauer class. -/
theorem finiteTensorInvariant_apply (a : finiteTensorH2OfExtension (K := K) L v) :
    finiteTensorInvariant (K := K) L v a =
      finitePlaceBrauerInvariantEquiv K v (finiteTensorH2ToBrauerOfExtension (K := K) L v a) :=
  AddMonoidHom.comp_apply (finitePlaceBrauerInvariantEquiv K v).toAddMonoidHom
    (finiteTensorH2ToBrauerOfExtension (K := K) L v) a

end Evaluation

variable {K : Type} [Field K] [NumberField K]
  (E : FiniteGaloisIntermediateField K (SeparableClosure K)) [NumberField E]
  (v : HeightOneSpectrum (𝓞 K))

local notation "d" => finiteTensorCompletedDegree E v

private theorem mem_range_circle_iff_of_card
    {A : Type*} [AddCommGroup A] (f : A →+ AddCircle (1 : ℚ))
    (hf : Function.Injective f) (m : ℕ) (hm : 0 < m) (hcard : Nat.card A = m)
    (z : AddCircle (1 : ℚ)) : z ∈ f.range ↔ m • z = 0 := by
  let : Finite A := Nat.finite_of_card_ne_zero (hcard.trans_ne hm.ne')
  let : NeZero m := ⟨hm.ne'⟩
  let j := zmodToRationalCircle m hm
  have hj := zmodToRationalCircle_injective m hm
  let : Finite j.range := Finite.of_surjective j.rangeRestrict j.rangeRestrict_surjective
  have hle : f.range ≤ j.range := by
    rintro _ ⟨x, rfl⟩
    apply (mem_range_zmodToRationalCircle_iff m hm (f x)).mpr
    rw [← hcard, ← map_nsmul, card_nsmul_eq_zero', map_zero]
  have hcardF : Nat.card f.range = m :=
    (Nat.card_congr (Equiv.ofInjective f hf)).symm.trans hcard
  have hcardJ : Nat.card j.range = m :=
    (Nat.card_congr (Equiv.ofInjective j hj)).symm.trans (Nat.card_zmod m)
  have heq := AddSubgroup.eq_of_le_of_card_ge hle (hcardJ.trans hcardF.symm).le
  rw [heq]
  exact mem_range_zmodToRationalCircle_iff m hm z

omit [NumberField ↥E.toIntermediateField] in
private theorem finiteTensorCompletedDegree_pos : 0 < d := by
  let F := ChosenFinitePlaceBaseCompletion (K := K) v
  let M := ChosenFinitePlaceLocalizedCompletion (K := K) (L := E) v
  let : Algebra F M :=
    finitePlaceLocalArtinLocalizedAlgebra v (chosenFinitePlaceExtension (L := E) v)
  let : FiniteDimensional F M :=
    localizedCompletionFiniteDimensional (HeightOneSpectrum.adicAbv K v)
      (RayClass.adicAbv_isNontrivial v) (chosenFinitePlaceExtension (L := E) v)
  let : Module.Free F M := Module.Free.of_divisionRing (K := F) (V := M)
  exact (Module.finrank_pos_iff_of_free F M).mpr inferInstance

omit [NumberField ↥E.toIntermediateField] in
/-- A finite tensor class realizes an invariant exactly when multiplication
by the actual completed local degree kills that invariant. -/
theorem mem_range_finiteTensorInvariant_iff (z : AddCircle (1 : ℚ)) :
    z ∈ (finiteTensorInvariant (E : Type) v).range ↔ d • z = 0 :=
  mem_range_circle_iff_of_card (A := finiteTensorH2OfExtension (E : Type) v)
    (finiteTensorInvariant (E : Type) v) (finiteTensorInvariant_injective (E : Type) v)
    d (finiteTensorCompletedDegree_pos E v) (finiteTensorH2_card E v) z

omit [NumberField ↥E.toIntermediateField] in
/-- A value annihilated by the completed degree has a finite tensor preimage. -/
theorem exists_finiteTensorInvariant_eq_of_nsmul_eq_zero (z : AddCircle (1 : ℚ))
    (hz : d • z = 0) :
    ∃ a : finiteTensorH2OfExtension (K := K) (E : Type) v,
      finitePlaceBrauerInvariantEquiv K v
        (finiteTensorH2ToBrauerOfExtension (K := K) (E : Type) v a) = z := by
  obtain ⟨a, ha⟩ := (mem_range_finiteTensorInvariant_iff (K := K) E v z).mpr hz
  exact ⟨a, (finiteTensorInvariant_apply (K := K) (E : Type) v a).symm.trans ha⟩

end ClassFieldTheory.Brauer

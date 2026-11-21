/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RankOneArtinConductor
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.ConductorCounting
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Character conductor multiplicities and the different in a finite completion -/

@[expose] public section

open scoped NumberField ValuativeRel IsMulCommutative

noncomputable section

namespace GlobalClassFieldTheory.GlobalClassFields

open NumberField IsDedekindDomain AlgebraicNumberTheory.Valuations
open LocalFieldTheory RamificationTheory.LocalField Reciprocity
open LocalFieldTheory.IsNonarchimedeanLocalField
open HilbertRamification RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

private theorem exists_localDifferent_eq_pow_ramificationSum
    (A B : Type*) [Field A] [Field B] [Algebra A B] [FiniteDimensional A B] [IsGalois A B]
    [ValuativeRel A] [TopologicalSpace A] [IsNonarchimedeanLocalField A] :
    let base := localCompleteDVF A
    let target := chosenLocalExtensionCompleteDVF A B
    let : IsScalarTower base.valuationSubring target.valuationSubring B :=
      IsScalarTower.of_algebraMap_eq' rfl
    ∃ N : ℕ, localLowerRamificationGroup A B (N : ℝ) = ⊥ ∧
      RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
        base target = target.maximalIdeal ^
          (∑ n ∈ Finset.range N, (Nat.card (localLowerRamificationGroup A B (n : ℝ)) - 1)) := by
  intro base target towerOwner
  let : IsScalarTower base.valuationSubring A B := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable base target
  let : Finite base.residueField := by
    change Finite 𝓀[A]
    infer_instance
  let : Algebra.IsSeparable base.residueField target.residueField := by
    let : FiniteDimensional base.residueField target.residueField :=
      residueField_finiteDimensional_of_moduleFinite base target
    infer_instance
  obtain ⟨N, hN, hd⟩ := exists_differentIdeal_eq_maximalIdeal_pow_lowerRamificationSum base target
    (chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension A B)
  exact ⟨N, hN N le_rfl, hd⟩

private theorem sum_character_conductors_from_lower_weights
    {A B : Type*} [CommGroup A] [Finite A] [Group B]
    [HasEnoughRootsOfUnity ℂ (Monoid.exponent A)] (i : B →* A)
    (hi : Function.Injective i) (G : ℕ → Subgroup B) (N : ℕ)
    (c : (A →* ℂˣ) → ℕ) (e : ℕ)
    (hweight : ∀ χ : A →* ℂˣ,
      (∑ n ∈ Finset.range N,
        @ite ℕ (G n ≤ χ.ker.comap i) (Classical.propDecidable _) 0 (Nat.card (G n))) =
        e * c χ) :
    e * (∑ᶠ χ, c χ) = Nat.card A * ∑ n ∈ Finset.range N, (Nat.card (G n) - 1) := by
  classical
  let : Fintype (A →* ℂˣ) := Fintype.ofFinite _
  let weight (χ : A →* ℂˣ) (n : ℕ) :=
    if G n ≤ χ.ker.comap i then 0 else Nat.card (G n)
  calc
    e * (∑ᶠ χ, c χ) = ∑ χ, ∑ n ∈ Finset.range N, weight χ n := by
      rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
      exact Finset.sum_congr rfl fun χ _ => (hweight χ).symm
    _ = ∑ n ∈ Finset.range N, ∑ χ, weight χ n := Finset.sum_comm
    _ = Nat.card A * ∑ n ∈ Finset.range N, (Nat.card (G n) - 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      have h := LocalClassFieldTheory.finsum_character_ramificationLayerWeight A ℂ ((G n).map i)
      rw [finsum_eq_sum_of_fintype, Subgroup.card_map_of_injective hi] at h
      simp only [Subgroup.map_le_iff_le_comap] at h
      exact h

/-- At a finite place, the inertia order times the sum of the global
character conductor exponents is the global Galois order times the exponent
of the actual different of the chosen completed extension. -/
theorem exists_completedDifferent_eq_pow_and_card_mul_finsum_characterConductor_of_extension
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv K v) L) :
    let vK := HeightOneSpectrum.adicAbv K v
    let E := LocalizedCompletion vK w
    let : Algebra vK.Completion E := finitePlaceLocalArtinLocalizedAlgebra v w
    let : FiniteDimensional vK.Completion E := finitePlaceLocalArtinFiniteDimensional v w
    let : IsAbelianGalois vK.Completion E := finitePlaceLocalArtinIsAbelianGalois v w
      (inferInstance : FiniteDimensional K L)
    let : ValuativeRel vK.Completion := finitePlaceLocalArtinCompletionValuativeRel v
    let : IsNonarchimedeanLocalField vK.Completion :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    let base := localCompleteDVF vK.Completion
    let target := chosenLocalExtensionCompleteDVF vK.Completion E
    let : IsScalarTower base.valuationSubring target.valuationSubring E :=
      IsScalarTower.of_algebraMap_eq' rfl
    ∃ d : ℕ,
      RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
        base target = target.maximalIdeal ^ d ∧
      Nat.card (localLowerRamificationGroup vK.Completion E 0) *
        (∑ᶠ χ : Gal(L/K) →* ℂˣ, (abelianCharacterConductor K L χ).finitePart v) =
        Nat.card Gal(L/K) * d := by
  intro vK E algebraOwner finiteOwner abelianOwner valuationOwner localFieldOwner
    base target towerOwner
  classical
  obtain ⟨N, hN, hd⟩ := exists_localDifferent_eq_pow_ramificationSum vK.Completion E
  let G := localLowerRamificationGroup vK.Completion E
  let c (χ : Gal(L/K) →* ℂˣ) := (abelianCharacterConductor K L χ).finitePart v
  let d := ∑ n ∈ Finset.range N, (Nat.card (G (n : ℝ)) - 1)
  refine ⟨d, hd, ?_⟩
  let i : Gal(E/vK.Completion) →* Gal(L/K) := finitePlaceLocalToGlobalMonoidHom v w
  have hi : Function.Injective i := by
    let e := decompositionGroupEquivAlgebraicLocalizationAut vK (RayClass.adicAbv_isNontrivial v) w
    exact Subtype.val_injective.comp e.symm.injective
  let a := Nat.card Gal(L/K)
  let : NeZero a := ⟨Finite.card_pos.ne'⟩
  let : NeZero (a : ℂ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne a)⟩
  let : HasEnoughRootsOfUnity ℂ a := IsSepClosed.hasEnoughRootsOfUnity ℂ a
  let : HasEnoughRootsOfUnity ℂ (Monoid.exponent Gal(L/K)) :=
    HasEnoughRootsOfUnity.of_dvd ℂ (n := a) (Group.exponent_dvd_nat_card (G := Gal(L/K)))
  have hweight (χ : Gal(L/K) →* ℂˣ) :
      (∑ n ∈ Finset.range N,
        @ite ℕ (G (n : ℝ) ≤ χ.ker.comap i) (Classical.propDecidable _) 0
          (Nat.card (G (n : ℝ)))) = Nat.card (G 0) * c χ := by
    have h := rankOneCharacter_sum_lowerWeights_eq_conductor_mul_inertia_of_extension χ v w N
      (show G (N : ℝ) ≤ χ.ker.comap i from hN.le.trans bot_le)
    dsimp (config := { instances := true, zetaDelta := true }) only [G, i, c, vK, E]
    with_reducible exact h
  exact sum_character_conductors_from_lower_weights i hi (fun n => G (n : ℝ)) N c
    (Nat.card (G 0)) hweight

end GlobalClassFieldTheory.GlobalClassFields

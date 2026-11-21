/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianCharacterConductor
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianLocalConductorComparison
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FinitePlaceArtinFiltration
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteLocalGlobalArtinCompatibility
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.WeightedArtinConductor
public import Mathlib.Basic.Complex.Basic

/-!
# Ramification of rank-one Artin characters

The conductor of the idele class character determines exactly which upper
ramification subgroups the Galois character kills. At real places the
conductor records the action of the local Artin value of negative one.
-/

@[expose] public section

open scoped NumberField ValuativeRel

noncomputable section

namespace GlobalClassFieldTheory.GlobalClassFields

open NumberField IsDedekindDomain AlgebraicNumberTheory.Valuations
open LocalFieldTheory RamificationTheory.LocalField Reciprocity
open RamificationTheory.HilbertRamification.Higher
open RamificationTheory.DiscreteValuationField.DVF (HasUniqueValuationExtension)

universe u v

variable {K : Type u} {L : Type v} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The rank-one character kills an actual local upper group exactly when
the ceiling of its index is at least the finite conductor exponent. -/
theorem rankOneCharacter_upperRamificationGroup_le_ker_iff_of_extension
    (χ : Gal(L/K) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv K v) L) (t : ℝ) (ht : 0 ≤ t) :
    let vK := HeightOneSpectrum.adicAbv K v
    let E := LocalizedCompletion vK w
    let : Algebra vK.Completion E := finitePlaceLocalArtinLocalizedAlgebra v w
    let : FiniteDimensional vK.Completion E := finitePlaceLocalArtinFiniteDimensional v w
    let : IsAbelianGalois vK.Completion E := finitePlaceLocalArtinIsAbelianGalois v w
      (inferInstance : FiniteDimensional K L)
    let : ValuativeRel vK.Completion := finitePlaceLocalArtinCompletionValuativeRel v
    let : IsNonarchimedeanLocalField vK.Completion :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    (localUpperRamificationGroup vK.Completion E t).map (finitePlaceLocalToGlobalMonoidHom v w) ≤
      χ.ker ↔ (abelianCharacterConductor K L χ).finitePart v ≤ ⌈t⌉₊ := by
  intro vK E algebraOwner finiteOwner abelianOwner valuationOwner localFieldOwner
  let H := abelianCharacterConductorialSubgroup K L χ
  have himage :
      (RayClass.localHigherUnitClassSubgroup v ⌈t⌉₊).map (globalNormResidueMonoidHom K L) =
        (localUpperRamificationGroup vK.Completion E t).map
          (finitePlaceLocalToGlobalMonoidHom v w) := by
    rw [RayClass.localHigherUnitClassSubgroup, Subgroup.map_map]
    have h := globalNormResidueMonoidHom_finitePlaceIdeleClass_fieldPrincipalUnits_of_extension
      (K := K) (L := L) v w t ht
    change ((fieldPrincipalUnits vK.Completion ⌈t⌉₊).map
        (_root_.finitePlaceCompletionUnitsContinuousMulEquiv v).toMonoidHom).map
          ((globalNormResidueMonoidHom K L).comp (IdeleGroup.finitePlaceIdeleClass v)) = _ at h
    dsimp only [vK] at h
    rw [finitePlaceFieldPrincipalUnits_map_eq_localHigherUnitGroup v ⌈t⌉₊] at h
    exact h
  rw [← himage, Subgroup.map_le_iff_le_comap]
  change RayClass.localHigherUnitClassSubgroup v ⌈t⌉₊ ≤ H.val ↔
    H.narrowFiniteConductor v ≤ ⌈t⌉₊
  rw [H.narrowFiniteConductor_apply_eq_narrowFiniteLocalConductorExponent]
  constructor
  · exact H.narrowFiniteLocalConductorExponent_le v
  · intro h
    refine le_trans ?_ (H.narrowFiniteLocalConductorExponent_spec v)
    exact Subgroup.map_mono (ClassFieldTheory.rayLocalHigherUnitGroup_antitone v h)

private theorem localizedLowerWeights_eq_card_inertia_mul_of_upperCut
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (H : Subgroup Gal(E/F)) (c N : ℕ) (hN : localLowerRamificationGroup F E N ≤ H)
    (hupper : ∀ t : ℝ, 0 ≤ t → (localUpperRamificationGroup F E t ≤ H ↔ c ≤ ⌈t⌉₊)) :
    (∑ n ∈ Finset.range N,
        @ite ℕ (localLowerRamificationGroup F E n ≤ H) (Classical.propDecidable _) 0
          (Nat.card (localLowerRamificationGroup F E n))) =
      Nat.card (localLowerRamificationGroup F E 0) * c := by
  classical
  let base := (localCompleteDVF F).toDVF
  let target := (chosenLocalExtensionCompleteDVF F E).toDVF
  let : base.valuation.HasExtension target.valuation :=
    chosenLocalExtensionCompleteDVF_hasExtension F E
  let witness : HasUniqueValuationExtension.{u, u, v, 0, 0} base target :=
    chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension F E
  let filtration := lowerRamificationFiltrationOfUniqueExtension
    (base := base) (target := target) witness
  have hcut (s : ℝ) (hs : 0 ≤ s) :
      filtration.lower ⌈s⌉₊ ≤ H ↔ c ≤ ⌈filtration.herbrandFunction s⌉₊ := by
    have ht := filtration.herbrandFunction_nonneg hs
    have hu := hupper (filtration.herbrandFunction s) ht
    have hlocal : localUpperRamificationGroup F E (filtration.herbrandFunction s) =
        filtration.lower ⌈s⌉₊ := by
      exact (upperRamificationGroupOfUniqueExtension_herbrandFunction witness s).trans
        (lowerRamificationGroup_eq_ceil_of_nonneg witness s hs)
    rwa [← hlocal]
  have hsum := filtration.sum_lowerWeights_eq_card_inertia_mul_of_herbrandCut H c N hN hcut
  change (∑ n ∈ Finset.range N,
      @ite ℕ (filtration.lower n ≤ H) (Classical.propDecidable _) 0
        (Nat.card (filtration.lower n))) = _
  have hzero : filtration.lower 0 = localLowerRamificationGroup F E (0 : ℕ) := rfl
  rw [Nat.cast_zero] at hzero
  rw [← hzero]
  exact hsum

/-- The lower-numbering Artin sum for the actual localized character is its
finite idele conductor multiplied by the inertia order. The index bound can
be any level at which the character is already trivial on the lower group. -/
theorem rankOneCharacter_sum_lowerWeights_eq_conductor_mul_inertia_of_extension
    (χ : Gal(L/K) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv K v) L) (N : ℕ) :
    let vK := HeightOneSpectrum.adicAbv K v
    let E := LocalizedCompletion vK w
    let : Algebra vK.Completion E := finitePlaceLocalArtinLocalizedAlgebra v w
    let : FiniteDimensional vK.Completion E := finitePlaceLocalArtinFiniteDimensional v w
    let : IsAbelianGalois vK.Completion E := finitePlaceLocalArtinIsAbelianGalois v w
      (inferInstance : FiniteDimensional K L)
    let : ValuativeRel vK.Completion := finitePlaceLocalArtinCompletionValuativeRel v
    let : IsNonarchimedeanLocalField vK.Completion :=
      finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
    let G := localLowerRamificationGroup vK.Completion E
    let f : Gal(E/vK.Completion) →* Gal(L/K) := finitePlaceLocalToGlobalMonoidHom v w
    let H : Subgroup Gal(E/vK.Completion) := χ.ker.comap f
    G (N : ℝ) ≤ H →
      (∑ n ∈ Finset.range N,
        @ite ℕ (G (n : ℝ) ≤ H) (Classical.propDecidable _) 0 (Nat.card (G (n : ℝ)))) =
        Nat.card (G 0) * (abelianCharacterConductor K L χ).finitePart v := by
  intro vK E algebraOwner finiteOwner abelianOwner valuationOwner localFieldOwner G f H hN
  let c := (abelianCharacterConductor K L χ).finitePart v
  have hupper (t : ℝ) (ht : 0 ≤ t) :
      localUpperRamificationGroup vK.Completion E t ≤ H ↔ c ≤ ⌈t⌉₊ := by
    have h := rankOneCharacter_upperRamificationGroup_le_ker_iff_of_extension χ v w t ht
    dsimp only at h
    exact (Subgroup.map_le_iff_le_comap (f := f) (H := χ.ker)).symm.trans h
  have result := localizedLowerWeights_eq_card_inertia_mul_of_upperCut
    (F := vK.Completion) (E := ↥E) H c N hN hupper
  with_reducible exact result

/-- A real place belongs to the conductor exactly when the character is
nontrivial on its local Artin value of negative one. At a ramified real
place that value is the chosen complex conjugation. -/
theorem rankOneCharacter_mem_infinitePart_iff
    (χ : Gal(L/K) →* ℂˣ) (v : RayClass.RealPlace K) :
    v ∈ (abelianCharacterConductor K L χ).infinitePart ↔
      χ (chosenInfinitePlaceArtinMonoidHom (K := K) (L := L) v.1
        (-1 : v.1.Completionˣ)) ≠ 1 := by
  let H := abelianCharacterConductorialSubgroup K L χ
  let a := chosenInfinitePlaceArtinMonoidHom (K := K) (L := L) v.1
  let i := IdeleGroup.infinitePlaceIdeleClass v.1
  have hArtin (x : v.1.Completionˣ) : globalNormResidueMonoidHom K L (i x) = a x :=
    DFunLike.congr_fun
      (globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass (K := K) (L := L) v.1) x
  change v ∈ H.fullConductorInfinitePart ↔ χ (a (-1 : v.1.Completionˣ)) ≠ 1
  rw [H.mem_fullConductorInfinitePart_iff]
  apply not_congr
  constructor
  · intro h
    have hneg := h (show i (-1 : v.1.Completionˣ) ∈ i.range from ⟨-1, rfl⟩)
    change χ (globalNormResidueMonoidHom K L (i (-1 : v.1.Completionˣ))) = 1 at hneg
    rwa [hArtin] at hneg
  · intro hneg _ hx
    obtain ⟨x, rfl⟩ := hx
    change χ (globalNormResidueMonoidHom K L (i x)) = 1
    rw [hArtin]
    let e := InfinitePlace.Completion.ringEquivRealOfIsReal v.2
    rcases lt_or_gt_of_ne ((map_ne_zero e).2 (Units.ne_zero x)) with hx | hx
    · have hpos : 0 < e (((-1 : v.1.Completionˣ) * x : v.1.Completionˣ) : v.1.Completion) := by
        change 0 < e ((-1 : v.1.Completion) * (x : v.1.Completion))
        rw [map_mul, map_neg, map_one, neg_one_mul]
        exact neg_pos.mpr hx
      have h := congrArg χ
        (chosenInfinitePlaceArtinMonoidHom_eq_one_of_real_pos (K := K) (L := L)
          v.1 v.2 ((-1 : v.1.Completionˣ) * x) hpos)
      change χ (a ((-1 : v.1.Completionˣ) * x)) = χ 1 at h
      rwa [a.map_mul, χ.map_mul, hneg, one_mul, χ.map_one] at h
    · rw [show a x = 1 from
        chosenInfinitePlaceArtinMonoidHom_eq_one_of_real_pos (K := K) (L := L) v.1 v.2 x hx,
        χ.map_one]

end GlobalClassFieldTheory.GlobalClassFields

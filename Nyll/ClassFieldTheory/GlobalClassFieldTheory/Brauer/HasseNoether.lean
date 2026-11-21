/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.CyclicRepresentatives
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.FiniteCyclicArtin
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.InfiniteCyclicArtin

/-! # The Brauer–Hasse–Noether sequence of the original continuous Brauer groups -/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField GlobalClassFieldTheory.Reciprocity
open scoped BigOperators DirectSum IsMulCommutative NumberField

namespace ClassFieldTheory.Brauer

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- At every place the arithmetic local invariant detects the completion's Brauer group. -/
theorem placeBrauerInvariant_injective (w : Place K) :
    Function.Injective (placeBrauerInvariant K w) := by
  cases w with
  | inl v => exact (finitePlaceBrauerInvariantEquiv K v).injective
  | inr v =>
    by_cases hv : v.IsReal
    · simpa only [placeBrauerInvariant, dite_eq_left hv] using realPlaceBrauerInvariant_injective hv
    · let : Subsingleton (Br v.Completion) := complexPlace_br_subsingleton
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)
      exact fun _ _ _ => Subsingleton.elim _ _

private theorem placeBrauerInvariant_localization_cyclic
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) [NumberField E]
    [IsCyclic Gal(E/K)] [IsAbelianGalois K E]
    (g : Gal(E/K)) (hg : ∀ σ : Gal(E/K), σ ∈ Subgroup.zpowers g) (a : Kˣ) (w : Place K) :
    placeBrauerInvariant K w (localization K (cyclicBrauerClass E g hg a) w) =
      finiteCyclicArithmeticCharacter g hg (Additive.ofMul (placeUnitArtin K E w
        (placeIdeleComponent K w (IdeleGroup.principalIdele K a)))) := by
  rw [localization_apply]
  cases w with
  | inl v =>
    have ha : IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K a) =
        Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a := Units.ext rfl
    change _ = finiteCyclicArithmeticCharacter g hg (Additive.ofMul
      (arithmeticChosenFinitePlaceArtinMonoidHom K E v
        (IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K a))))
    rw [ha]
    exact placeBrauerInvariant_finite_cyclicBrauerClass K E g hg v a
  | inr v =>
    have ha : IdeleGroup.infiniteComponent v (IdeleGroup.principalIdele K a) =
        Units.map (algebraMap K v.Completion).toMonoidHom a := Units.ext rfl
    change _ = finiteCyclicArithmeticCharacter g hg (Additive.ofMul
      (arithmeticChosenInfinitePlaceArtinMonoidHom K E v
        (IdeleGroup.infiniteComponent v (IdeleGroup.principalIdele K a))))
    rw [ha]
    exact placeBrauerInvariant_infinite_cyclicBrauerClass v E g hg a

private theorem finiteCyclicArithmeticCharacter_prod {G ι : Type*} [CommGroup G] [Fintype G]
    (g : G) (hg : ∀ σ : G, σ ∈ Subgroup.zpowers g) (S : Finset ι) (f : ι → G) :
    finiteCyclicArithmeticCharacter g hg (Additive.ofMul (∏ w ∈ S, f w)) =
      ∑ w ∈ S, finiteCyclicArithmeticCharacter g hg (Additive.ofMul (f w)) :=
  map_prod (finiteCyclicArithmeticCharacter g hg).toMultiplicativeRight f S

/-- A finitely supported family whose actual invariants sum to zero is
the localization of a global cyclic carry class. -/
theorem ker_sumLocalInv_le_range_localization : (sumLocalInv K).ker ≤ (localization K).range := by
  classical
  intro x hx
  have hsum : sumLocalInv K x = 0 := hx
  obtain ⟨E, hcyc, hfin, hreal⟩ := exists_cyclicStage_for_localBrauerTuple K x
  let : NumberField E := NumberField.of_module_finite K E
  let : IsCyclic Gal(E/K) := hcyc
  let : IsAbelianGalois K E := IsAbelianGalois.of_isCyclic K E
  let : CommGroup Gal(E/K) := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(E/K))
  let χ := finiteCyclicArithmeticCharacter g hg
  have hrep (w : Place K) : ∃ b : (placeCompletion K w)ˣ,
      χ (Additive.ofMul (placeUnitArtin K E w b)) = placeBrauerInvariant K w (x w) := by
    cases w with
    | inl v => exact exists_placeUnitArtin_finite_invariant K E g hg v (x (Sum.inl v)) (hfin v)
    | inr v => exact exists_placeUnitArtin_infinite_invariant v E g hg (hreal v) (x (Sum.inr v))
  choose b hb using hrep
  let S := x.support
  let a := supportedLocalUnitIdele K S b
  have ha : arithmeticGlobalArtinMonoidHom K E a = 1 := by
    apply Additive.ofMul.injective
    apply finiteCyclicArithmeticCharacter_injective g hg
    rw [arithmeticGlobalArtin_supportedLocalUnitIdele, finiteCyclicArithmeticCharacter_prod]
    change (∑ w ∈ S, χ (Additive.ofMul (placeUnitArtin K E w (b w)))) = χ 0
    rw [map_zero, ← hsum, sumLocalInv_apply]
    exact Finset.sum_congr rfl (fun w _ => hb w)
  obtain ⟨a₀, ha₀⟩ := exists_principalUnit_of_arithmeticGlobalArtin_eq_one K E a ha
  refine ⟨cyclicBrauerClass E g hg a₀, ?_⟩
  apply DirectSum.ext
  intro w
  apply placeBrauerInvariant_injective K w
  rw [placeBrauerInvariant_localization_cyclic K E g hg a₀ w, ha₀ w,
    placeIdeleComponent_supportedLocalUnitIdele]
  by_cases hw : w ∈ S
  · rw [ite_eq_left hw]
    exact hb w
  · rw [ite_eq_right hw, map_one, DFinsupp.notMem_support_iff.mp hw]
    exact (map_zero χ).trans (map_zero (placeBrauerInvariant K w)).symm

private theorem sumLocalInv_localization_cyclic_eq_zero
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) [NumberField E]
    [IsCyclic Gal(E/K)] [IsAbelianGalois K E]
    (g : Gal(E/K)) (hg : ∀ σ : Gal(E/K), σ ∈ Subgroup.zpowers g) (a : Kˣ) :
    sumLocalInv K (localization K (cyclicBrauerClass E g hg a)) = 0 := by
  classical
  let : CommGroup Gal(E/K) := IsCyclic.commGroup
  let x := localization K (cyclicBrauerClass E g hg a)
  let χ := finiteCyclicArithmeticCharacter g hg
  let p := IdeleGroup.principalIdele K a
  let f (w : Place K) := placeUnitArtin K E w (placeIdeleComponent K w p)
  have hc (w : Place K) : placeBrauerInvariant K w (x w) = χ (Additive.ofMul (f w)) :=
    placeBrauerInvariant_localization_cyclic K E g hg a w
  have hf (w : Place K) (hw : w ∉ x.support) : f w = 1 := by
    apply Additive.ofMul.injective
    apply finiteCyclicArithmeticCharacter_injective g hg
    change χ (Additive.ofMul (f w)) = χ 0
    rw [← hc w, DFinsupp.notMem_support_iff.mp hw, map_zero, map_zero]
  have hprod : (∏ w ∈ x.support, f w) = 1 :=
    (arithmeticGlobalArtin_eq_prod_placeUnitArtin K E p x.support hf).symm.trans
      (arithmeticGlobalArtinMonoidHom_principalIdele K E a)
  change sumLocalInv K x = 0
  calc
    _ = ∑ w ∈ x.support, χ (Additive.ofMul (f w)) :=
      (sumLocalInv_apply K x).trans (Finset.sum_congr rfl (fun w _ => hc w))
    _ = χ (Additive.ofMul (∏ w ∈ x.support, f w)) :=
      (finiteCyclicArithmeticCharacter_prod g hg x.support f).symm
    _ = 0 := by rw [hprod]; exact map_zero χ

variable (K₀ : Type u) [Field K₀] [NumberField K₀]

/-- The arithmetic invariants of all local restrictions of a global class sum to zero. -/
theorem sumLocalInv_localization_eq_zero (x : Br K₀) : sumLocalInv K₀ (localization K₀ x) = 0 := by
  obtain ⟨E, hcyc, g, hg, a, ha⟩ := exists_cyclicBrauerRepresentative x
  let : NumberField E := NumberField.of_module_finite K₀ E
  let : IsCyclic Gal(E/K₀) := hcyc
  let : IsAbelianGalois K₀ E := IsAbelianGalois.of_isCyclic K₀ E
  rw [← ha]
  exact sumLocalInv_localization_cyclic_eq_zero K₀ E g hg a

/-- The image of actual global localization is the kernel of the sum of the local invariants. -/
theorem localization_range_eq_sumLocalInv_ker : (localization K₀).range = (sumLocalInv K₀).ker := by
  refine le_antisymm ?_ (ker_sumLocalInv_le_range_localization K₀)
  rintro x ⟨a, rfl⟩
  exact sumLocalInv_localization_eq_zero K₀ a

/-- A finite-support family of actual local classes has a unique global
preimage precisely when its arithmetic invariants sum to zero. -/
theorem existsUnique_localization_iff (x : ⨁ w : Place K₀, Br (placeCompletion K₀ w)) :
    (∃! a : Br K₀, localization K₀ a = x) ↔ sumLocalInv K₀ x = 0 := by
  constructor
  · rintro ⟨a, rfl, _⟩
    exact sumLocalInv_localization_eq_zero K₀ a
  · intro hx
    obtain ⟨a, ha⟩ := ker_sumLocalInv_le_range_localization K₀
      (show x ∈ (sumLocalInv K₀).ker from hx)
    exact ⟨a, ha, fun b hb => localization_injective K₀ (hb.trans ha.symm)⟩

/-- The continuous Brauer–Hasse–Noether sequence is exact, with the canonical actual maps. -/
theorem brauerHasseNoether : Function.Injective (localization K₀) ∧
    Function.Exact (localization K₀) (sumLocalInv K₀) ∧ Function.Surjective (sumLocalInv K₀) :=
  ⟨localization_injective K₀,
    AddMonoidHom.exact_iff.mpr (localization_range_eq_sumLocalInv_ker K₀).symm,
    sumLocalInv_surjective K₀⟩

/-- Actual localization in the standard finite-direct-sum and infinite-product form. -/
def finiteInfiniteLocalization : Br K₀ →+ FiniteInfiniteLocalBrauer K₀ :=
  (finiteInfiniteLocalBrauerEquiv K₀).toAddMonoidHom.comp (localization K₀)

/-- The same arithmetic invariants summed on the standard product of local groups. -/
def sumFiniteInfiniteLocalInv : FiniteInfiniteLocalBrauer K₀ →+ AddCircle (1 : ℚ) :=
  (sumLocalInv K₀).comp (finiteInfiniteLocalBrauerEquiv K₀).symm.toAddMonoidHom

/-- The Brauer–Hasse–Noether sequence in finite-direct-sum and infinite-product form. -/
theorem brauerHasseNoether_finiteInfinite : Function.Injective (finiteInfiniteLocalization K₀) ∧
    Function.Exact (finiteInfiniteLocalization K₀) (sumFiniteInfiniteLocalInv K₀) ∧
    Function.Surjective (sumFiniteInfiniteLocalInv K₀) := by
  let e := finiteInfiniteLocalBrauerEquiv K₀
  refine ⟨e.injective.comp (localization_injective K₀), fun x => ?_,
    (sumLocalInv_surjective K₀).comp e.symm.surjective⟩
  change sumLocalInv K₀ (e.symm x) = 0 ↔ ∃ a, e (localization K₀ a) = x
  constructor
  · intro hx
    obtain ⟨a, ha, _⟩ := (existsUnique_localization_iff K₀ (e.symm x)).2 hx
    exact ⟨a, (congrArg e ha).trans (e.apply_symm_apply x)⟩
  · rintro ⟨a, rfl⟩
    rw [e.symm_apply_apply]
    exact sumLocalInv_localization_eq_zero K₀ a

end ClassFieldTheory.Brauer

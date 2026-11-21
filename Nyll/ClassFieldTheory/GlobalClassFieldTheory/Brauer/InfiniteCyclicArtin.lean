/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.CyclicRestriction
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.ComplexPlace
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.InfiniteLocalizedStage
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.InvariantSum
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.ContinuousUnramified

/-! # The archimedean invariant of an actual global cyclic carry class -/

@[expose] public section

noncomputable section

open AlgebraicNumberTheory.Valuations ClassFieldTower.Cohomology HilbertRamification
open GlobalClassFieldTheory.Reciprocity LocalClassFieldTheory LocalFieldTheory NumberField
open scoped NumberField

attribute [local instance] AbsoluteValue.Completion.algebraOfLiesOver

namespace ClassFieldTheory.Brauer

universe u

variable {K : Type u} [Field K] [NumberField K]
    (v : InfinitePlace K) (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    [NumberField E] [IsCyclic Gal(E/K)] [IsAbelianGalois K E]
    (g : Gal(E/K)) (hg : ∀ σ : Gal(E/K), σ ∈ Subgroup.zpowers g)

omit [IsCyclic Gal(↥E.toIntermediateField/K)] in
private theorem localNorm_iff_infinitePlaceArtin_eq_one (a : Kˣ) :
    Units.map (algebraMap K v.1.Completion).toMonoidHom a ∈
      localizedCompletionNormSubgroup v.1 (chosenInfinitePlaceExtension v E) ↔
      arithmeticChosenInfinitePlaceArtinMonoidHom K E v
        (Units.map (algebraMap K v.Completion).toMonoidHom a) = 1 := by
  let w := chosenInfinitePlaceExtension v E
  let F := v.1.Completion
  let M := LocalizedCompletion v.1 w
  let : Algebra F M := localizedCompletionBaseAlgebra v.1 w
  let aF := Units.map (algebraMap K F).toMonoidHom a
  let aV := Units.map (algebraMap K v.Completion).toMonoidHom a
  change aF ∈ localNormSubgroup F M ↔
    arithmeticChosenInfinitePlaceArtinMonoidHom K E v aV = 1
  rw [arithmeticChosenInfinitePlaceArtinMonoidHom_apply, inv_eq_one,
    ← MonoidHom.mem_ker, chosenInfinitePlaceArtinMonoidHom_ker]
  change aF ∈ localNormSubgroup F M ↔ aF ∈ localTensorNormSubgroup (L := E) v.1
  exact Iff.of_eq (congrArg (fun H : Subgroup Fˣ => aF ∈ H)
    (localTensorNormSubgroup_eq_localNormSubgroup (K := K) (L := E) v.1 w v.isNontrivial).symm)

/-- At the actual infinite completion a cyclic carry vanishes precisely
when the arithmetic local Artin symbol of its base unit is trivial. -/
theorem infinitePlaceRestriction_cyclicBrauerClass_eq_zero_iff_artin (a : Kˣ) :
    infinitePlaceRestriction K v (cyclicBrauerClass E g hg a) = 0 ↔
      arithmeticChosenInfinitePlaceArtinMonoidHom K E v
        (Units.map (algebraMap K v.Completion).toMonoidHom a) = 1 := by
  let w := chosenInfinitePlaceExtension v E
  exact (infinitePlaceRestriction_cyclicBrauerClass_eq_zero_iff_localizedNorm
    v E w g hg a).trans (localNorm_iff_infinitePlaceArtin_eq_one v E a)


private theorem rationalCircle_eq_of_two_nsmul_eq_zero {x y : AddCircle (1 : ℚ)}
    (hx : 2 • x = 0) (hy : 2 • y = 0) (hz : x = 0 ↔ y = 0) : x = y := by
  let f := zmodToRationalCircle 2 (by decide)
  obtain ⟨a, rfl⟩ := (mem_range_zmodToRationalCircle_iff 2 (by decide) x).mpr hx
  obtain ⟨b, rfl⟩ := (mem_range_zmodToRationalCircle_iff 2 (by decide) y).mpr hy
  change f a = f b
  apply congrArg f
  have hzero (k : ZMod 2) : f k = 0 ↔ k = 0 := by
    rw [← map_zero f]
    exact (zmodToRationalCircle_injective 2 (by decide)).eq_iff
  have hab : a = 0 ↔ b = 0 := (hzero a).symm.trans (hz.trans (hzero b))
  have hzmod (k : ZMod 2) : k = 0 ∨ k = 1 := by
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hzmod a with ha | ha <;> rcases hzmod b with hb | hb
  · exact ha.trans hb.symm
  · exact ((by decide : (1 : ZMod 2) ≠ 0) (hb.symm.trans (hab.mp ha))).elim
  · exact ((by decide : (1 : ZMod 2) ≠ 0) (ha.symm.trans (hab.mpr hb))).elim
  · exact ha.trans hb.symm

private theorem cyclicArithmeticCharacter_eq_zero_iff {G : Type u} [Group G] [Fintype G]
    (g : G) (hg : ∀ σ : G, σ ∈ Subgroup.zpowers g) (σ : G) :
    finiteCyclicArithmeticCharacter g hg (Additive.ofMul σ) = 0 ↔ σ = 1 := by
  let χ := finiteCyclicArithmeticCharacter g hg
  change χ (Additive.ofMul σ) = 0 ↔ _
  rw [← map_zero χ, (finiteCyclicArithmeticCharacter_injective g hg).eq_iff]
  exact Additive.ofMul.injective.eq_iff

omit [NumberField K] [NumberField ↥E.toIntermediateField]
    [IsCyclic Gal(↥E.toIntermediateField/K)] in
private theorem two_nsmul_infiniteCyclicArtin (b : v.Completionˣ) :
    2 • finiteCyclicArithmeticCharacter g hg (Additive.ofMul
      (arithmeticChosenInfinitePlaceArtinMonoidHom K E v b)) = 0 := by
  let σ := arithmeticChosenInfinitePlaceArtinMonoidHom K E v b
  have hσ : σ ^ 2 = 1 := by
    change arithmeticChosenInfinitePlaceArtinMonoidHom K E v b ^ 2 = 1
    rw [arithmeticChosenInfinitePlaceArtinMonoidHom_apply, inv_pow,
      chosenInfinitePlaceArtinMonoidHom_sq, inv_one]
  rw [← map_nsmul]
  change finiteCyclicArithmeticCharacter g hg (Additive.ofMul (σ ^ 2)) = 0
  rw [hσ]
  exact map_zero _

/-- The actual archimedean invariant of a cyclic carry evaluates the specified
cyclic character at the arithmetic local Artin symbol of the same base unit. -/
theorem placeBrauerInvariant_infinite_cyclicBrauerClass (a : Kˣ) :
    placeBrauerInvariant K (Sum.inr v) (infinitePlaceRestriction K v (cyclicBrauerClass E g hg a)) =
      finiteCyclicArithmeticCharacter g hg (Additive.ofMul
        (arithmeticChosenInfinitePlaceArtinMonoidHom K E v
          (Units.map (algebraMap K v.Completion).toMonoidHom a))) := by
  classical
  let aV := Units.map (algebraMap K v.Completion).toMonoidHom a
  let σ := arithmeticChosenInfinitePlaceArtinMonoidHom K E v aV
  let x := infinitePlaceRestriction K v (cyclicBrauerClass E g hg a)
  let χ := finiteCyclicArithmeticCharacter g hg
  have hzero : x = 0 ↔ σ = 1 :=
    infinitePlaceRestriction_cyclicBrauerClass_eq_zero_iff_artin v E g hg a
  have hχzero : χ (Additive.ofMul σ) = 0 ↔ σ = 1 := cyclicArithmeticCharacter_eq_zero_iff g hg σ
  change (if hv : v.IsReal then realPlaceBrauerInvariant hv else 0) x = χ (Additive.ofMul σ)
  by_cases hv : v.IsReal
  · rw [dite_eq_left hv]
    apply rationalCircle_eq_of_two_nsmul_eq_zero
    · exact (mem_range_realPlaceBrauerInvariant_iff hv _).mp ⟨x, rfl⟩
    · exact two_nsmul_infiniteCyclicArtin v E g hg aV
    · rw [hχzero, ← hzero, ← map_zero (realPlaceBrauerInvariant hv),
        (realPlaceBrauerInvariant_injective hv).eq_iff]
  · rw [dite_eq_right hv, AddMonoidHom.zero_apply]
    apply (hχzero.mpr (hzero.mp ?_)).symm
    change infinitePlaceRestriction K v (cyclicBrauerClass E g hg a) = 0
    have hc := InfinitePlace.not_isReal_iff_isComplex.mp hv
    rw [infinitePlaceRestriction_eq_zero_of_isComplex hc, AddMonoidHom.zero_apply]

omit [IsCyclic Gal(↥E.toIntermediateField/K)] in
/-- If the cyclic stage ramifies at the given real place, every local Brauer
invariant is the cyclic character of an actual archimedean Artin value. -/
theorem exists_placeUnitArtin_infinite_invariant
    (hRamifies : v.IsReal → (chosenInfinitePlaceAbove (L := E) v).IsRamified K)
    (x : Br v.Completion) : ∃ b : v.Completionˣ,
      finiteCyclicArithmeticCharacter g hg (Additive.ofMul
        (arithmeticChosenInfinitePlaceArtinMonoidHom K E v b)) =
      placeBrauerInvariant K (Sum.inr v) x := by
  classical
  let χ := finiteCyclicArithmeticCharacter g hg
  change ∃ b : v.Completionˣ, χ (Additive.ofMul
      (arithmeticChosenInfinitePlaceArtinMonoidHom K E v b)) =
      (if hv : v.IsReal then realPlaceBrauerInvariant hv else 0) x
  by_cases hv : v.IsReal
  · rw [dite_eq_left hv]
    by_cases hx : realPlaceBrauerInvariant hv x = 0
    · refine ⟨1, ?_⟩
      rw [map_one, hx]
      exact map_zero χ
    · let b : v.Completionˣ := -1
      refine ⟨b, ?_⟩
      apply rationalCircle_eq_of_two_nsmul_eq_zero
      · exact two_nsmul_infiniteCyclicArtin v E g hg b
      · exact (mem_range_realPlaceBrauerInvariant_iff hv _).mp ⟨x, rfl⟩
      · have hb : arithmeticChosenInfinitePlaceArtinMonoidHom K E v b ≠ 1 := by
          intro h
          rw [arithmeticChosenInfinitePlaceArtinMonoidHom_apply, inv_eq_one] at h
          exact chosenInfinitePlaceArtinMonoidHom_neg_one_ne_one_of_ramified v (hRamifies hv) h
        rw [cyclicArithmeticCharacter_eq_zero_iff g hg]
        exact ⟨fun h => (hb h).elim, fun h => (hx h).elim⟩
  · rw [dite_eq_right hv, AddMonoidHom.zero_apply]
    refine ⟨1, ?_⟩
    rw [map_one]
    exact map_zero χ

end ClassFieldTheory.Brauer

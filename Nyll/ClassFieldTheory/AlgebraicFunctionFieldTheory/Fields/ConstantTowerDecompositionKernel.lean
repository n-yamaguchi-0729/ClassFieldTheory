/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantExtension
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Decomposition
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantDecompositionGenerator
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionTower
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantFieldExtension
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantFrobeniusPlace
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteConstantsInClosure
import Nyll.GaloisCohomology.FieldTheory.FiniteAlgebraicConstants

/-!
# Lifting constant Frobenius powers to decomposition automorphisms

In the actual constant tower over `L`, powers of the original finite-base
Frobenius by the degree of a place lift to automorphisms fixing `L` and the
chosen upper place. The lift is the corresponding power of the actual
full-constant Frobenius. The change of exponent is the residue-degree formula
under extension of constants.
-/

noncomputable section

namespace FunctionField

open AlgebraicCurve
open scoped AlgebraicCurve.Place

variable (k L Ω : Type*) [Field k] [Finite k] [Field L] [Field Ω]
    [Algebra k L] [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L]
    [FunctionField k L] [Algebra L Ω] [Algebra k Ω] [IsScalarTower k L Ω]
    [IsSepClosed Ω]

/-- The constant actions of the actual decomposition group are exactly the
powers of base-field Frobenius allowed by the degree of the place. -/
theorem constantExtensionRestriction_map_decompositionGroup (n : ℕ) [NeZero n]
    (W : Place k (fullConstantDegreeStage k L Ω n)) :
    let _ : Algebra.EssFiniteType k L := essFiniteType k L
    let _ : Finite (algebraicClosure k L) :=
      FieldTheory.finite_algebraicClosure_of_finite_base k L
    let _ : IsScalarTower k (algebraicClosure k L) Ω :=
      IsScalarTower.to₁₂₄ k (algebraicClosure k L) L Ω
    let C : IntermediateField k Ω :=
      (finiteConstantsInClosure (algebraicClosure k L) Ω n).toIntermediateField.restrictScalars k
    let _ : FiniteDimensional k C := FiniteDimensional.trans k (algebraicClosure k L)
      (finiteConstantsInClosure (algebraicClosure k L) Ω n).toIntermediateField
    let _ : Fintype k := Fintype.ofFinite k
    let g : Gal(C/k) := FiniteField.frobeniusAlgEquivOfAlgebraic k C
    (IdeleGroup.decompositionGroup (K := L) W).map
        (constantExtensionRestriction (K := L) C) =
      Subgroup.zpowers (g ^ (W.restrict L).deg) := by
  intro hess hA hkAΩ C hCfinite hkFintype g
  let A := algebraicClosure k L
  let D := (finiteConstantsInClosure A Ω n).toIntermediateField
  let W' : Place A (fullConstantDegreeStage k L Ω n) := W.extendConstants A
  let d : ℕ := (W'.restrict L).deg
  let r : ℕ := Module.finrank k A
  let φ : Gal((fullConstantDegreeStage k L Ω n)/L) :=
    fullConstantDegreeFrobenius k L Ω n
  let R : Gal((fullConstantDegreeStage k L Ω n)/L) →* Gal(C/k) :=
    constantExtensionRestriction (K := L) C
  change (IdeleGroup.decompositionGroup (K := L) W).map R =
    Subgroup.zpowers (g ^ (W.restrict L).deg)
  have hφ : R φ = g ^ r := by
    apply AlgEquiv.ext
    intro c
    have hcomm := constantExtensionRestriction_commutes (K := L) C φ c
    have hfrob := fullConstantExtensionFrobenius_constant (k := k) (K := L) D c
    have hvalue : ((R φ c : C) : Ω) = (c : Ω) ^ Nat.card A :=
      (congrArg (fun x : IntermediateField.adjoin L (C : Set Ω) => (x : Ω)) hcomm).trans
        (congrArg (fun x : IntermediateField.adjoin L (D : Set Ω) => (x : Ω)) hfrob)
    let _ : Fintype A := Fintype.ofFinite A
    have hcard : Nat.card A = Fintype.card k ^ r := by
      rw [Nat.card_eq_fintype_card]
      exact Module.card_eq_pow_finrank
    have hiterate : (g ^ r) c = c ^ Nat.card A := by
      change (FiniteField.frobeniusAlgEquivOfAlgebraic k C ^ r) c = c ^ Nat.card A
      rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, hcard]
    exact Subtype.ext (hvalue.trans (congrArg (fun x : C => (x : Ω)) hiterate).symm)
  have hw : (W'.restrict L).forgetConstants (K := k) = W.restrict L := Place.ext rfl
  have hdegree : (W.restrict L).deg = r * d := by
    have h := Place.deg_forgetConstants (K := k) (W'.restrict L)
    rw [hw] at h
    exact h
  have hdecomposition : IdeleGroup.decompositionGroup (K := L) W =
      IdeleGroup.decompositionGroup (K := L) W' := by
    apply Subgroup.ext
    intro σ
    constructor
    · intro hσ
      apply Place.ext
      have h := congrArg Place.toValuationSubring hσ
      rw [SemilinearAut.smul_toValuationSubring] at h ⊢
      exact h
    · intro hσ
      apply Place.ext
      have h := congrArg Place.toValuationSubring hσ
      rw [SemilinearAut.smul_toValuationSubring] at h ⊢
      exact h
  have hφdC : R (φ ^ d) =
      g ^ (W.restrict L).deg := by
    rw [map_pow, hφ, ← pow_mul, ← hdegree]
  rw [hdecomposition,
    decompositionGroup_fullConstantDegreeStage_eq_zpowers k L Ω n W',
    MonoidHom.map_zpowers]
  exact congrArg Subgroup.zpowers hφdC

/-- Every constant Frobenius power allowed by the degree of the place has an
actual lift fixing both the function field and the chosen upper place. -/
theorem exists_constantDecomposition_frobeniusPower_lift (n : ℕ) [NeZero n]
    (W : Place k (fullConstantDegreeStage k L Ω n)) :
    let _ : Algebra.EssFiniteType k L := essFiniteType k L
    let _ : Finite (algebraicClosure k L) :=
      FieldTheory.finite_algebraicClosure_of_finite_base k L
    let _ : IsScalarTower k (algebraicClosure k L) Ω :=
      IsScalarTower.to₁₂₄ k (algebraicClosure k L) L Ω
    let C : IntermediateField k Ω :=
      (finiteConstantsInClosure (algebraicClosure k L) Ω n).toIntermediateField.restrictScalars k
    let _ : FiniteDimensional k C := FiniteDimensional.trans k (algebraicClosure k L)
      (finiteConstantsInClosure (algebraicClosure k L) Ω n).toIntermediateField
    let _ : Fintype k := Fintype.ofFinite k
    let g : Gal(C/k) := FiniteField.frobeniusAlgEquivOfAlgebraic k C
    ∀ η : Gal(C/k), η ∈ Subgroup.zpowers (g ^ (W.restrict L).deg) →
      ∃ σ : Gal((fullConstantDegreeStage k L Ω n)/L),
        σ ∈ IdeleGroup.decompositionGroup (K := L) W ∧
          constantExtensionRestriction (K := L) C σ = η := by
  intro hess hA hkAΩ C hCfinite hkFintype g η hη
  have himage := constantExtensionRestriction_map_decompositionGroup k L Ω n W
  rw [← himage] at hη
  exact hη

end FunctionField

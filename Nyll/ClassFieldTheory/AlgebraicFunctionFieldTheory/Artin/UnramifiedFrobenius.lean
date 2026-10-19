/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Nyll.ClassFieldTheory.Algebra.RestrictedProduct.Valuation
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalResidueNormalization
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.DecompositionResidue
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Galois
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.NormOpen
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Divisor
import Nyll.AlgebraicCurves.Places.Ramification.CardFiberOverMulRamificationIndexMulInertiaDeg

/-!
# Arithmetic Frobenius in the actual decomposition group

At an unramified place, the local symbol of any order-one element is the
unique decomposition automorphism inducing arithmetic residue Frobenius.
The symbol of an arbitrary local element is its order power. Consequently
the Frobenius order is the residue degree and local norms are detected by
divisibility of the local order.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

private theorem exists_arithmeticDecompositionFrobenius
    (w : Place k L) (he : w.ramificationIndex K = 1) :
    ∃ σ : IdeleGroup.decompositionGroup (K := K) w,
      ∀ y : w.ResidueField, IdeleGroup.decompositionResidueAut (K := K) w σ y =
        y ^ Nat.card (w.restrict K).ResidueField := by
  let π : (w.restrict K).adicCompletionˣ :=
    RestrictedProduct.DiscreteValuation.chosenLocalOrderSection
      (w.restrict K).adicCompletion
      ((w.restrict K).heightOneSpectrum.valuedAdicCompletion_surjective K) 1
  exact ⟨localDecompositionArtin (K := K) w π,
    localDecompositionArtin_uniformizer_residue w he π
      (RestrictedProduct.DiscreteValuation.localOrder_chosenLocalOrderSection _ _ 1)⟩

/-- The arithmetic decomposition Frobenius at an unramified place. Its
existence is supplied by local reciprocity on an actual order-one element. -/
def unramifiedDecompositionFrobenius (w : Place k L) (he : w.ramificationIndex K = 1) :
    IdeleGroup.decompositionGroup (K := K) w :=
  Classical.choose (exists_arithmeticDecompositionFrobenius w he)

/-- The constructed automorphism acts by arithmetic Frobenius on residues. -/
theorem unramifiedDecompositionFrobenius_residue
    (w : Place k L) (he : w.ramificationIndex K = 1) (y : w.ResidueField) :
    IdeleGroup.decompositionResidueAut (K := K) w
        (unramifiedDecompositionFrobenius (K := K) w he) y =
      y ^ Nat.card (w.restrict K).ResidueField :=
  Classical.choose_spec (exists_arithmeticDecompositionFrobenius w he) y

/-- Powers of the arithmetic decomposition Frobenius act by the corresponding
iterates of residue Frobenius. -/
theorem unramifiedDecompositionFrobenius_pow_residue
    (w : Place k L) (he : w.ramificationIndex K = 1) (n : ℕ) (y : w.ResidueField) :
    IdeleGroup.decompositionResidueAut (K := K) w
        (unramifiedDecompositionFrobenius (K := K) w he ^ n) y =
      y ^ (Nat.card (w.restrict K).ResidueField ^ n) := by
  induction n generalizing y with
  | zero => simp only [pow_zero, map_one, AlgEquiv.one_apply, pow_one]
  | succ n ih =>
    rw [pow_succ, map_mul, AlgEquiv.mul_apply, ih,
      unramifiedDecompositionFrobenius_residue, ← pow_mul, pow_succ']

/-- Arithmetic residue action uniquely determines the unramified Frobenius. -/
theorem eq_unramifiedDecompositionFrobenius_iff
    (w : Place k L) (he : w.ramificationIndex K = 1)
    (σ : IdeleGroup.decompositionGroup (K := K) w) :
    σ = unramifiedDecompositionFrobenius (K := K) w he ↔
      ∀ y : w.ResidueField, IdeleGroup.decompositionResidueAut (K := K) w σ y =
        y ^ Nat.card (w.restrict K).ResidueField := by
  constructor
  · rintro rfl
    exact unramifiedDecompositionFrobenius_residue w he
  · intro hσ
    apply (decompositionResidueAut_bijective_of_ramificationIndex_eq_one w he).1
    apply AlgEquiv.ext
    intro y
    exact (hσ y).trans (unramifiedDecompositionFrobenius_residue w he y).symm

/-- An arbitrary local element gives the local-order power of arithmetic Frobenius. -/
theorem localDecompositionArtin_eq_unramifiedFrobenius_zpow
    (w : Place k L) (he : w.ramificationIndex K = 1)
    (x : (w.restrict K).adicCompletionˣ) :
    localDecompositionArtin (K := K) w x =
      unramifiedDecompositionFrobenius (K := K) w he ^
        (IdeleGroup.localOrder (w.restrict K) x).toAdd := by
  let π : (w.restrict K).adicCompletionˣ :=
    RestrictedProduct.DiscreteValuation.chosenLocalOrderSection
      (w.restrict K).adicCompletion
      ((w.restrict K).heightOneSpectrum.valuedAdicCompletion_surjective K) 1
  have hπ : (IdeleGroup.localOrder (w.restrict K) π).toAdd = 1 :=
    RestrictedProduct.DiscreteValuation.localOrder_chosenLocalOrderSection _ _ 1
  let m : ℤ := (IdeleGroup.localOrder (w.restrict K) x).toAdd
  let u : (w.restrict K).adicCompletionˣ := x / π ^ m
  have hu : (IdeleGroup.localOrder (w.restrict K) u).toAdd = 0 := by
    change (IdeleGroup.localOrder (w.restrict K) (x / π ^ m)).toAdd = 0
    rw [map_div, map_zpow, toAdd_div, toAdd_zpow, hπ, zsmul_eq_mul, mul_one]
    exact sub_self m
  obtain ⟨z, _, hz⟩ :=
    IdeleGroup.exists_integral_localNorm_eq_of_ramificationIndex_eq_one w he u
      ((IdeleGroup.localOrder_eq_zero_iff (w.restrict K) u).mp hu)
  have hlocal : localDecompositionArtin (K := K) w u = 1 := by
    change u ∈ (localDecompositionArtin (K := K) w).toMonoidHom.ker
    rw [localDecompositionArtin_ker]
    exact ⟨z, hz⟩
  change localDecompositionArtin (K := K) w (x / π ^ m) = 1 at hlocal
  rw [map_div, map_zpow, div_eq_one] at hlocal
  have hπF : localDecompositionArtin (K := K) w π =
      unramifiedDecompositionFrobenius (K := K) w he :=
    (eq_unramifiedDecompositionFrobenius_iff w he _).mpr
      (localDecompositionArtin_uniformizer_residue w he π hπ)
  rw [hπF] at hlocal
  exact hlocal

/-- Arithmetic Frobenius generates the entire unramified decomposition group. -/
theorem zpowers_unramifiedDecompositionFrobenius
    (w : Place k L) (he : w.ramificationIndex K = 1) :
    Subgroup.zpowers (unramifiedDecompositionFrobenius (K := K) w he) = ⊤ := by
  apply top_unique
  intro σ _
  obtain ⟨x, rfl⟩ := localDecompositionArtin_surjective (K := K) w σ
  exact Subgroup.mem_zpowers_iff.mpr
    ⟨(IdeleGroup.localOrder (w.restrict K) x).toAdd,
      (localDecompositionArtin_eq_unramifiedFrobenius_zpow w he x).symm⟩

/-- The Frobenius order is the actual residue extension degree. -/
theorem orderOf_unramifiedDecompositionFrobenius
    (w : Place k L) (he : w.ramificationIndex K = 1) :
    orderOf (unramifiedDecompositionFrobenius (K := K) w he) = w.inertiaDeg K := by
  rw [orderOf_eq_card_of_zpowers_eq_top (zpowers_unramifiedDecompositionFrobenius w he),
    IdeleGroup.decompositionGroup_card_eq_ramificationIndex_mul_inertiaDeg, he, one_mul]

/-- Arithmetic Frobenius is trivial exactly when the unramified residue degree is one. -/
theorem unramifiedDecompositionFrobenius_eq_one_iff
    (w : Place k L) (he : w.ramificationIndex K = 1) :
    unramifiedDecompositionFrobenius (K := K) w he = 1 ↔ w.inertiaDeg K = 1 := by
  rw [← orderOf_eq_one_iff, orderOf_unramifiedDecompositionFrobenius w he]

/-- The number of places above the base place times the Frobenius order is
the global extension degree. -/
theorem card_fiberOver_mul_orderOf_unramifiedFrobenius
    (w : Place k L) (he : w.ramificationIndex K = 1) :
    ((w.restrict K).fiberOver L).card *
        orderOf (unramifiedDecompositionFrobenius (K := K) w he) = Module.finrank K L := by
  rw [orderOf_unramifiedDecompositionFrobenius w he]
  have h := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg (w.restrict K) w rfl
  rw [he, one_mul] at h
  exact h

/-- In an unramified completed extension, an element is a norm exactly when
its local order is divisible by the residue degree. -/
theorem mem_localNorm_range_iff_inertiaDeg_dvd
    (w : Place k L) (he : w.ramificationIndex K = 1)
    (x : (w.restrict K).adicCompletionˣ) :
    x ∈ (IdeleGroup.localNorm (K := K) w).range ↔
      (w.inertiaDeg K : ℤ) ∣ (IdeleGroup.localOrder (w.restrict K) x).toAdd := by
  rw [← localDecompositionArtin_ker]
  change localDecompositionArtin (K := K) w x = 1 ↔ _
  rw [localDecompositionArtin_eq_unramifiedFrobenius_zpow w he,
    ← orderOf_dvd_iff_zpow_eq_one, orderOf_unramifiedDecompositionFrobenius w he]

end FunctionField

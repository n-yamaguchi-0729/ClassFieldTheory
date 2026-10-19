/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.PrimeIndexTransport
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.NormRefinementTower
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.NormIndex
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.TameNormCofinality
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormTopology

/-!
# Actual norm cofinality for every ordinary open finite-index subgroup

Induct on the actual index. A prime-index open overgroup has an actual
class field. Pullback along its norm strictly decreases the index.
The inductively constructed relative extension is brought back to the
original base by the shared normal-closure abelian refinement.
-/

noncomputable section
open AlgebraicCurve

namespace FunctionField

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K] [IsSepClosure K Ω]

/-- Every finite-index open subgroup for the ordinary idele-class topology
contains an actual finite abelian norm subgroup in the supplied closure. -/
theorem exists_finiteAbelian_norm_le_of_open
    (H : Subgroup (IdeleClassGroup k K)) [H.FiniteIndex]
    (hH : IsOpen (H : Set (IdeleClassGroup k K))) :
    ∃ A : FiniteGaloisIntermediateField K Ω, IsAbelianGalois K A ∧
      (have _ : HasPrincipalDivisors k A :=
        (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K A).toHasPrincipalDivisors
      (IdeleClassGroup.norm (k := k) (K := K) (L := A)).range ≤ H) := by
  classical
  induction hn : H.index using Nat.strong_induction_on generalizing K Ω with
  | h n ih =>
    by_cases htop : H = ⊤
    · have hindex : H.index = 1 := Subgroup.index_eq_one.mpr htop
      have hne : NeZero (H.index : k) := ⟨by rw [hindex, Nat.cast_one]; exact one_ne_zero⟩
      exact exists_finiteAbelian_norm_le_of_primeToCharacteristic k K Ω H hH
    obtain ⟨p, U, hp, hHU, hUopen, hUindex⟩ :=
      exists_open_prime_index_overgroup k K H hH htop
    have hUfinite : U.FiniteIndex := Subgroup.finiteIndex_iff.mpr (by
      rw [hUindex]
      exact hp.ne_zero)
    have hUprime : U.index.Prime := by rw [hUindex]; exact hp
    obtain ⟨L, hLabelian, hLnorm⟩ :=
      exists_classField_of_prime_index_in_sepClosure k K Ω U hUopen hUprime
    have hkLΩ : IsScalarTower k L Ω := IsScalarTower.to₁₃₄ k K L Ω
    let presentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K L
    let aRL : Algebra (RatFunc k) L := presentation.val
    have hkRL : IsScalarTower k (RatFunc k) L := presentation.property.1
    have hfunctionL : FunctionField k L := presentation.property.2
    have hcurveL : IsCurveOver k L := isCurveOver k L
    have hclosed : IsSepClosed Ω := IsSepClosure.sep_closed K
    have hclosureL : IsSepClosure L Ω :=
      ⟨hclosed, Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩
    let N : IdeleClassGroup k L →* IdeleClassGroup k K :=
      IdeleClassGroup.norm (k := k) (K := K) (L := L)
    let H' : Subgroup (IdeleClassGroup k L) := H.comap N
    have hH'finite : H'.FiniteIndex := inferInstance
    have hHnorm : H ≤ N.range := hHU.trans hLnorm.symm.le
    have hdegree : 1 < Module.finrank K L := by
      rw [← finiteAbelian_norm_index k K L, hLnorm, hUindex]
      exact hp.one_lt
    obtain ⟨hH'open, hlt⟩ :=
      finiteAbelian_norm_comap_open_index_lt k K L H hH hHnorm hdegree
    obtain ⟨E, hEabelian, hEnorm⟩ :=
      ih H'.index (hlt.trans_eq hn) L Ω H' hH'open rfl
    apply exists_finiteAbelian_norm_le_of_relative k K Ω L.toIntermediateField H E
    intro hEprincipal
    exact hEnorm

end FunctionField

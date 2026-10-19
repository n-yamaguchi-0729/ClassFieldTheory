/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.PrimePowerNormCofinality
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.TameNormCofinality
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SubextensionCorrespondence
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.RayPowerQuotient
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Algebra.CharP.Basic

/-!
# Actual class fields at prime index

The characteristic-prime construction and the prime-to-characteristic
construction cover every prime index. A nontrivial finite idele-class
quotient supplies an open overgroup of such an index.
-/

noncomputable section

namespace FunctionField

open scoped IsMulCommutative

variable (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]

omit [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] in
/-- Every nontrivial finite-index open subgroup is contained in an actual
open subgroup of prime index. -/
theorem exists_open_prime_index_overgroup
    (H : Subgroup (IdeleClassGroup k K)) [H.FiniteIndex]
    (hH : IsOpen (H : Set (IdeleClassGroup k K))) (hne : H ≠ ⊤) :
    ∃ (p : ℕ) (U : Subgroup (IdeleClassGroup k K)),
      p.Prime ∧ H ≤ U ∧ IsOpen (U : Set (IdeleClassGroup k K)) ∧ U.index = p := by
  -- Both successive quotients use the canonical quotient commutative group.
  let classGroup : CommGroup (IdeleClassGroup k K) :=
    QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup k K)
  let quotientGroup : CommGroup (IdeleClassGroup k K ⧸ H) :=
    QuotientGroup.Quotient.commGroup H
  have hn : H.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.ne_one_iff_exists_prime_dvd.mp hn
  obtain ⟨V, hV, _⟩ :=
    Group.IsNilpotent.exists_normal_index_eq_of_dvd_card
      (G := IdeleClassGroup k K ⧸ H) hpdvd
  let U : Subgroup (IdeleClassGroup k K) := V.comap (QuotientGroup.mk' H)
  have hHU : H ≤ U := by
    intro c hc
    change (c : IdeleClassGroup k K ⧸ H) ∈ V
    rw [(QuotientGroup.eq_one_iff c).mpr hc]
    exact V.one_mem
  exact ⟨p, U, hp, hHU, Subgroup.isOpen_mono hHU hH,
    (V.index_comap_of_surjective (QuotientGroup.mk'_surjective H)).trans hV⟩

/-- An ordinary open subgroup of prime index is the exact norm image of an
actual finite abelian extension in the fixed separable closure. -/
theorem exists_classField_of_prime_index
    (H : Subgroup (IdeleClassGroup k K)) [H.FiniteIndex]
    (hH : IsOpen (H : Set (IdeleClassGroup k K))) (hp : H.index.Prime) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    ∃ (E : IntermediateField K (SeparableClosure K)) (_ : FiniteDimensional K E)
      (_ : IsAbelianGalois K E),
      (IdeleClassGroup.norm (k := k) (K := K) (L := E)).range = H := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  by_cases hchar : (H.index : k) = 0
  · have hpFact : Fact H.index.Prime := ⟨hp⟩
    have hcharK : CharP K H.index := (CharP.charP_iff_prime_eq_zero hp).mpr (by
      rw [← map_natCast (algebraMap k K), hchar, map_zero])
    obtain ⟨m, _, hpower⟩ := RayClass.exists_powerRaySubgroup_le H hH
    obtain ⟨E, hEfinite, hEabelian, hEnorm⟩ :=
      exists_finiteAbelian_norm_le_powerRay_prime k K H.index m
    obtain ⟨F, hFfinite, hFabelian, _, hFnorm⟩ :=
      exists_subextension_norm_eq k K E H (hEnorm.trans hpower)
    exact ⟨F, hFfinite, hFabelian, hFnorm⟩
  · have hne : NeZero (H.index : k) := ⟨hchar⟩
    exact exists_classField_of_primeToCharacteristic k K H hH

end FunctionField

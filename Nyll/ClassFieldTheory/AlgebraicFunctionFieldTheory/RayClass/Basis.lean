/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Tactic.Choose
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Constructions
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.LocalField
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.CompactUnits
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Topology
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Topology
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups

/-!
# Ray congruence subgroups inside arbitrary open subgroups

An open idele subgroup contains the integral tail outside some finite set of
places. At each of those places its inverse image under the local inclusion is
an actual open local subgroup, so the existing principal-unit theorem supplies
a depth. Decomposing an idele into its finite local product and integral tail
then proves containment of the associated ray congruence subgroup.

This avoids an extra proof of the principal-unit neighborhood theorem. The same
construction applies to the inverse image of an open idele-class subgroup.
-/

noncomputable section

namespace FunctionField.RayClass

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

private theorem exists_finset_integral_tail_le (H : Subgroup (IdeleGroup k K))
    (hH : IsOpen (H : Set (IdeleGroup k K))) :
    ∃ T : Finset (AlgebraicCurve.Place k K), ∀ a : IdeleGroup k K,
      (∀ v, a v ∈ v.adicCompletionIntegers.units) →
      (∀ v ∈ T, a v = 1) → a ∈ H := by
  let D := fun v : AlgebraicCurve.Place k K => v.adicCompletionIntegers.units
  let s : (∀ v, D v) → IdeleGroup k K :=
    RestrictedProduct.structureMap
      (fun v : AlgebraicCurve.Place k K => v.adicCompletionˣ)
      (fun v => (D v : Set v.adicCompletionˣ)) Filter.cofinite
  have hs : Continuous s := RestrictedProduct.isEmbedding_structureMap.continuous
  have hsone : s 1 = 1 := by
    apply RestrictedProduct.ext
    intro v
    rfl
  have hOne : (1 : ∀ v, D v) ∈ s ⁻¹' (H : Set (IdeleGroup k K)) := by
    change s 1 ∈ H
    rw [hsone]
    exact H.one_mem
  obtain ⟨T, U, hU, hTU⟩ :=
    isOpen_pi_iff.mp (hH.preimage hs) (1 : ∀ v, D v) hOne
  refine ⟨T, fun a ha htail => ?_⟩
  let d : ∀ v, D v := fun v => ⟨a v, ha v⟩
  have hd : d ∈ (T : Set (AlgebraicCurve.Place k K)).pi U := by
    intro v hv
    have hdv : d v = 1 := Subtype.ext (htail v hv)
    rw [hdv]
    exact (hU v hv).2
  have hdH := hTU hd
  have hsd : s d = a := by
    apply RestrictedProduct.ext
    intro v
    rfl
  change s d ∈ H at hdH
  exact hsd ▸ hdH

/-- Shared finite-local-product decomposition. The tail condition is the
actual product-neighborhood consequence proved above. -/
private theorem congruenceSubgroup_le_of_integral_tail
    (m : Modulus k K) (H : Subgroup (IdeleGroup k K))
    (T : Finset (AlgebraicCurve.Place k K))
    (htail : ∀ a : IdeleGroup k K,
      (∀ v, a v ∈ v.adicCompletionIntegers.units) →
      (∀ v ∈ T, a v = 1) → a ∈ H)
    (hlocal : ∀ v ∈ T, localHigherUnitGroup v (m v) ≤ H.comap (IdeleGroup.placeIdele v)) :
    congruenceSubgroup m ≤ H := by
  classical
  intro a ha
  have haInt : ∀ v, a v ∈ v.adicCompletionIntegers.units :=
    congruenceSubgroup_le_integralSubgroup m ha
  let z : IdeleGroup k K := ∏ v ∈ T, IdeleGroup.placeIdele v (a v)
  have hzH : z ∈ H := by
    apply H.prod_mem
    intro v hv
    exact hlocal v hv (ha v)
  have hz (v : AlgebraicCurve.Place k K) :
      z v = if v ∈ T then a v else 1 := by
    change IdeleGroup.component v (∏ w ∈ T, IdeleGroup.placeIdele w (a w)) = _
    rw [map_prod]
    by_cases hv : v ∈ T
    · rw [ite_eq_left hv]
      calc
        (∏ w ∈ T, IdeleGroup.component v (IdeleGroup.placeIdele w (a w))) =
            IdeleGroup.component v (IdeleGroup.placeIdele v (a v)) := by
          apply Finset.prod_eq_single_of_mem v hv
          intro w _ hw
          exact IdeleGroup.component_placeIdele_of_ne w v (a w) hw.symm
        _ = a v := IdeleGroup.component_placeIdele_same v (a v)
    · rw [ite_eq_right hv]
      apply Finset.prod_eq_one
      intro w hw
      exact IdeleGroup.component_placeIdele_of_ne w v (a w) (fun h => hv (h.symm ▸ hw))
  have hzInt (v : AlgebraicCurve.Place k K) :
      z v ∈ v.adicCompletionIntegers.units := by
    rw [hz]
    by_cases hv : v ∈ T
    · rw [ite_eq_left hv]
      exact haInt v
    · rw [ite_eq_right hv]
      exact (v.adicCompletionIntegers.units).one_mem
  have haTail : a / z ∈ H := htail (a / z)
    (fun v => (v.adicCompletionIntegers.units).div_mem (haInt v) (hzInt v)) (by
      intro v hv
      change a v / z v = 1
      rw [hz, ite_eq_left hv, div_self'])
  have hmul : (a / z) * z ∈ H := H.mul_mem haTail hzH
  simpa only [div_mul_cancel] using hmul

/-- Containment of a ray congruence subgroup in an ordinary open subgroup
is equivalent to containment of every prescribed local higher-unit group. -/
theorem congruenceSubgroup_le_iff
    (m : Modulus k K) (H : Subgroup (IdeleGroup k K))
    (hH : IsOpen (H : Set (IdeleGroup k K))) :
    congruenceSubgroup m ≤ H ↔
      ∀ v, localHigherUnitGroup v (m v) ≤ H.comap (IdeleGroup.placeIdele v) := by
  constructor
  · intro h v x hx
    apply h
    intro w
    change IdeleGroup.component w (IdeleGroup.placeIdele v x) ∈ localHigherUnitGroup w (m w)
    by_cases hw : w = v
    · subst w
      rw [IdeleGroup.component_placeIdele_same]
      exact hx
    · rw [IdeleGroup.component_placeIdele_of_ne v w x hw]
      exact (localHigherUnitGroup w (m w)).one_mem
  · intro h
    obtain ⟨T, htail⟩ := exists_finset_integral_tail_le H hH
    exact congruenceSubgroup_le_of_integral_tail m H T htail (fun v _ => h v)

variable [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K]

/-- Every open all-place idele subgroup contains a ray congruence subgroup. -/
theorem exists_congruenceSubgroup_le (H : Subgroup (IdeleGroup k K))
    (hH : IsOpen (H : Set (IdeleGroup k K))) :
    ∃ m : Modulus k K, congruenceSubgroup m ≤ H := by
  classical
  obtain ⟨T, htail⟩ := exists_finset_integral_tail_le H hH
  have hlocal (v : T) : ∃ n : ℕ,
      localHigherUnitGroup v.1 n ≤ H.comap (IdeleGroup.placeIdele v.1) := by
    let : ValuativeRel v.1.adicCompletion := placeCompletionValuativeRel v.1
    have : IsNonarchimedeanLocalField v.1.adicCompletion :=
      placeCompletion_isNonarchimedeanLocalField v.1
    obtain ⟨n, _, hn⟩ := LocalFieldTheory.exists_fieldPrincipalUnits_le_of_isOpen
      v.1.adicCompletion (H.comap (IdeleGroup.placeIdele v.1))
      (hH.preimage (IdeleGroup.continuous_placeIdele v.1))
    exact ⟨n, hn⟩
  choose n hn using hlocal
  let exponent : AlgebraicCurve.Place k K → ℕ :=
    fun v => if hv : v ∈ T then n ⟨v, hv⟩ else 0
  have hsupport : ∀ v, exponent v ≠ 0 → v ∈ T := by
    intro v hv
    by_contra h
    exact hv (dite_eq_right h)
  let m : Modulus k K := Finsupp.onFinset T exponent hsupport
  have hmv (v : AlgebraicCurve.Place k K) (hv : v ∈ T) : m v = n ⟨v, hv⟩ := by
    change (if h : v ∈ T then n ⟨v, h⟩ else 0) = n ⟨v, hv⟩
    exact dite_eq_left hv
  refine ⟨m, congruenceSubgroup_le_of_integral_tail m H T htail ?_⟩
  intro v hv x hx
  apply hn ⟨v, hv⟩
  rw [← hmv v hv]
  exact hx


variable [AlgebraicCurve.HasPrincipalDivisors k K]

/-- Every open subgroup of the actual idele class group contains a ray subgroup. -/
theorem exists_rayClassSubgroup_le (H : Subgroup (IdeleClassGroup k K))
    (hH : IsOpen (H : Set (IdeleClassGroup k K))) :
    ∃ m : Modulus k K, rayClassSubgroup m ≤ H := by
  let pre : Subgroup (IdeleGroup k K) :=
    H.comap (IdeleClassGroup.mk (k := k) (K := K))
  have hopen : IsOpen (pre : Set (IdeleGroup k K)) :=
    hH.preimage QuotientGroup.continuous_mk
  obtain ⟨m, hm⟩ := exists_congruenceSubgroup_le pre hopen
  refine ⟨m, ?_⟩
  rintro c ⟨a, ha, rfl⟩
  exact hm ha

omit [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] in
/-- The class ray subgroup is contained in an ordinary open subgroup exactly
when all local higher units map into it under the actual local inclusions. -/
theorem rayClassSubgroup_le_iff
    (m : Modulus k K) (H : Subgroup (IdeleClassGroup k K))
    (hH : IsOpen (H : Set (IdeleClassGroup k K))) :
    rayClassSubgroup m ≤ H ↔
      ∀ v, localHigherUnitGroup v (m v) ≤
        H.comap ((IdeleClassGroup.mk (k := k) (K := K)).comp (IdeleGroup.placeIdele v)) := by
  rw [rayClassSubgroup, Subgroup.map_le_iff_le_comap]
  simpa only [Subgroup.comap_comap] using
    (congruenceSubgroup_le_iff m (H.comap (IdeleClassGroup.mk (k := k) (K := K)))
      (hH.preimage QuotientGroup.continuous_mk))

end FunctionField.RayClass

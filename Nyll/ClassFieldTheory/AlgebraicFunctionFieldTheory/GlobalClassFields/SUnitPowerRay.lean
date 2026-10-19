/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SUnitPowerClassSubgroup
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.RayPowerQuotient
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SupportedComponents
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve

/-!
# Local powers inside a prescribed ray-power subgroup

An actual S-idele whose S-components are powers is the product of an
actual idele power and a ray-congruent idele, when S contains the modulus
support. The finite-support idele construction is shared with the local
power quotient and norm constructions.
-/

noncomputable section
open AlgebraicCurve

namespace FunctionField.IdeleGroup

variable {k K : Type} [Field k] [Field K] [Algebra k K]
    [HasPrincipalDivisors k K]

/-- Local powers modulo the prescribed higher units give an actual
ray class times an actual global idele-class power. -/
theorem sIdeleClass_mem_powerRaySubgroup_of_local (n : ℕ)
    (S : Finset (Place k K)) (m : RayClass.Modulus k K) (hm : m.support ⊆ S)
    (a : sIdeles S)
    (ha : ∀ v : S, a.val v.val ∈
      (powMonoidHom (α := v.val.adicCompletionˣ) n).range ⊔
        RayClass.localHigherUnitGroup v.val (m v.val)) :
    sIdeleClass S a ∈ RayClass.powerRaySubgroup m n := by
  classical
  have hlocal (v : S) : ∃ x z : v.val.adicCompletionˣ,
      z ∈ RayClass.localHigherUnitGroup v.val (m v.val) ∧
        x ^ n * z = a.val v.val := by
    obtain ⟨y, ⟨x, rfl⟩, z, hz, hprod⟩ := Subgroup.mem_sup.mp (ha v)
    exact ⟨x, z, hz, hprod⟩
  choose x z hz hx using hlocal
  obtain ⟨b, hbin, hbout⟩ := exists_supported_sIdele S x
  let u : IdeleGroup k K := a.val / b.val ^ n
  have hu : u ∈ RayClass.congruenceSubgroup m := by
    intro v
    change component v u ∈ RayClass.localHigherUnitGroup v (m v)
    by_cases hv : v ∈ S
    · have hvu : component v u = z ⟨v, hv⟩ := by
        change component v (a.val / b.val ^ n) = z ⟨v, hv⟩
        rw [map_div, map_pow]
        change a.val v / (b.val v) ^ n = z ⟨v, hv⟩
        rw [hbin ⟨v, hv⟩, ← hx ⟨v, hv⟩, mul_div_cancel_left]
      rw [hvu]
      exact hz ⟨v, hv⟩
    · have hm0 : m v = 0 :=
        Finsupp.notMem_support_iff.mp (fun h => hv (hm h))
      rw [hm0, RayClass.localHigherUnitGroup_zero]
      change component v (a.val / b.val ^ n) ∈ v.adicCompletionIntegers.units
      rw [map_div, map_pow]
      change a.val v / (b.val v) ^ n ∈ v.adicCompletionIntegers.units
      rw [hbout v hv, one_pow, div_one]
      exact a.property v hv
  have hrayle : RayClass.rayClassSubgroup m ≤ RayClass.powerRaySubgroup m n :=
    le_sup_left
  have hpowle : (powMonoidHom (α := IdeleClassGroup k K) n).range ≤
      RayClass.powerRaySubgroup m n := le_sup_right
  have hU : IdeleClassGroup.mk (k := k) (K := K) u ∈
      RayClass.powerRaySubgroup m n :=
    hrayle (show IdeleClassGroup.mk (k := k) (K := K) u ∈
      RayClass.rayClassSubgroup m from ⟨u, hu, rfl⟩)
  have hB : (IdeleClassGroup.mk (k := k) (K := K) b.val) ^ n ∈
      RayClass.powerRaySubgroup m n :=
    hpowle ⟨IdeleClassGroup.mk (k := k) (K := K) b.val, rfl⟩
  change IdeleClassGroup.mk (k := k) (K := K) a.val ∈ _
  have hfactor : IdeleClassGroup.mk (k := k) (K := K) a.val =
      IdeleClassGroup.mk (k := k) (K := K) u *
        (IdeleClassGroup.mk (k := k) (K := K) b.val) ^ n := by
    rw [← map_pow, ← map_mul]
    exact congrArg (IdeleClassGroup.mk (k := k) (K := K))
      (div_mul_cancel a.val (b.val ^ n)).symm
  rw [hfactor]
  exact (RayClass.powerRaySubgroup m n).mul_mem hU hB

/-- A representative with power components over the modulus support gives
an actual ray class times an actual global idele-class power. -/
theorem powerClassSubgroup_le_powerRaySubgroup (n : ℕ+)
    (S : Finset (Place k K)) (m : RayClass.Modulus k K) (hm : m.support ⊆ S) :
    powerClassSubgroup (k := k) (K := K) n S ≤ RayClass.powerRaySubgroup m (n : ℕ) := by
  rintro c ⟨a, ha, rfl⟩
  apply sIdeleClass_mem_powerRaySubgroup_of_local (n : ℕ) S m hm a
  intro v
  exact Subgroup.mem_sup_left ((QuotientGroup.eq_one_iff _).mp (congrFun ha v))

variable [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K]

/-- The actual Picard presentation can contain a prescribed modulus support
and a place, while retaining surjectivity on idele classes. -/
theorem exists_supported_powerClassSubgroup_le (m : RayClass.Modulus k K) (n : ℕ+) :
    ∃ S : Finset (Place k K), S.Nonempty ∧
      Function.Surjective (sIdeleClass S) ∧
      powerClassSubgroup (k := k) (K := K) n S ≤
        RayClass.powerRaySubgroup m (n : ℕ) := by
  classical
  obtain ⟨S₀, hS₀⟩ := exists_finset_sIdeleClass_surjective k K
  obtain ⟨v⟩ := FunctionField.nonempty_place k K
  let S : Finset (Place k K) := insert v (S₀ ∪ m.support)
  have h₀ : S₀ ⊆ S := fun w hw => Finset.mem_insert_of_mem (Finset.mem_union_left _ hw)
  have hm : m.support ⊆ S :=
    fun w hw => Finset.mem_insert_of_mem (Finset.mem_union_right _ hw)
  have hS : Function.Surjective (sIdeleClass S) := by
    intro c
    obtain ⟨a, ha⟩ := hS₀ c
    exact ⟨⟨a.val, sIdeles_mono h₀ a.property⟩, ha⟩
  exact ⟨S, ⟨v, Finset.mem_insert_self _ _⟩, hS,
    powerClassSubgroup_le_powerRaySubgroup n S m hm⟩

end FunctionField.IdeleGroup

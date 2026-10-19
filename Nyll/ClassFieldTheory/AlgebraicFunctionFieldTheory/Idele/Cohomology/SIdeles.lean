/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.PicardGenerators
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SUnits

/-!
# S-ideles representing every idele class

Finite generation of the actual Picard group supplies a finite set of places outside
which every idele class has an integral representative. The kernel of this presentation
is precisely the diagonal group of actual S-units.
-/

noncomputable section

namespace FunctionField.IdeleGroup

open AlgebraicCurve

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Ideles integral and invertible at all places outside `S`. -/
def sIdeles (S : Finset (Place k K)) : Subgroup (IdeleGroup k K) where
  carrier := {a | ∀ v : Place k K, v ∉ S → a v ∈ v.adicCompletionIntegers.units}
  one_mem' := fun v _ => v.adicCompletionIntegers.units.one_mem
  mul_mem' := fun ha hb v hv => v.adicCompletionIntegers.units.mul_mem (ha v hv) (hb v hv)
  inv_mem' := fun ha v hv => v.adicCompletionIntegers.units.inv_mem (ha v hv)

/-- Membership in the S-idele group is support of the actual divisor. -/
theorem mem_sIdeles_iff (S : Finset (Place k K)) (a : IdeleGroup k K) :
    a ∈ sIdeles S ↔ (divisor (k := k) (K := K) a).toAdd.support ⊆ S := by
  constructor
  · intro ha v hv
    by_contra hvS
    have hz := (localOrder_eq_zero_iff v (a v)).mpr (ha v hvS)
    exact Finsupp.mem_support_iff.mp hv ((divisor_apply a v).trans hz)
  · intro ha v hv
    apply (localOrder_eq_zero_iff v (a v)).mp
    rw [← divisor_apply]
    exact Finsupp.notMem_support_iff.mp (fun h => hv (ha h))

/-- Enlarging the exceptional set enlarges the S-idele group. -/
theorem sIdeles_mono {S T : Finset (Place k K)} (hST : S ⊆ T) :
    sIdeles S ≤ sIdeles T :=
  fun _ ha v hv => ha v (fun h => hv (hST h))

variable [HasPrincipalDivisors k K]

/-- The diagonal S-unit map into the actual S-idele group. -/
def sUnitDiagonal (S : Finset (Place k K)) : SUnits.units k K S →* sIdeles S :=
  ((principalIdele k K).comp (SUnits.units k K S).subtype).codRestrict _ fun x v hv => by
    apply (localOrder_eq_zero_iff v _).mp
    exact (localOrder_algebraMap v (x : Kˣ)).trans (x.2 v hv)

/-- The actual map from S-ideles to idele classes. -/
def sIdeleClass (S : Finset (Place k K)) : sIdeles S →* IdeleClassGroup k K :=
  IdeleClassGroup.mk.comp (sIdeles S).subtype

/-- The kernel of the S-idele presentation consists exactly of diagonal S-units. -/
theorem range_sUnitDiagonal (S : Finset (Place k K)) :
    (sUnitDiagonal S).range = (sIdeleClass S).ker := by
  ext a
  change (∃ x, sUnitDiagonal S x = a) ↔
    IdeleClassGroup.mk (k := k) (K := K) (a : IdeleGroup k K) = 1
  change _ ↔ (QuotientGroup.mk (a : IdeleGroup k K) : IdeleClassGroup k K) = 1
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(x : Kˣ), rfl⟩
  · rintro ⟨x, hx⟩
    have hS : x ∈ SUnits.units k K S := by
      intro v hv
      rw [← localOrder_algebraMap v x]
      apply (localOrder_eq_zero_iff v _).mpr
      change principalIdele k K x v ∈ v.adicCompletionIntegers.units
      rw [hx]
      exact a.2 v hv
    exact ⟨⟨x, hS⟩, Subtype.ext hx⟩

/-- Divisors supported on `S` representing every Picard class make S-ideles surjective. -/
theorem sIdeleClass_surjective_of_picard (S : Finset (Place k K))
    (hS : ∀ c : Pic k K, ∃ D : Divisor k K, D.support ⊆ S ∧ H1Gm.mk D = c) :
    Function.Surjective (sIdeleClass S) := by
  intro c
  obtain ⟨a, rfl⟩ := IdeleClassGroup.mk_surjective c
  obtain ⟨D, hD, hclass⟩ := hS (divisorClass (k := k) (K := K) a).toAdd
  obtain ⟨b, hb⟩ := divisor_surjective (k := k) (K := K) (Multiplicative.ofAdd D)
  have hbS : b ∈ sIdeles S := (mem_sIdeles_iff S b).mpr (hb ▸ hD)
  have hquot : divisorClass (k := k) (K := K) (a / b) = 1 := by
    rw [map_div, div_eq_one]
    apply Multiplicative.ext
    change (divisorClass (k := k) (K := K) a).toAdd = H1Gm.mk (divisor (k := k) (K := K) b).toAdd
    rw [hb]
    exact hclass.symm
  obtain ⟨x, hx⟩ := (divisorClass_eq_one_iff_exists_integral (a / b)).mp hquot
  let d : sIdeles S := ⟨b * ((a / b) / principalIdele k K x),
    fun v hv => v.adicCompletionIntegers.units.mul_mem (hbS v hv) (hx v)⟩
  refine ⟨d, ?_⟩
  change IdeleClassGroup.mk (k := k) (K := K) (b * ((a / b) / principalIdele k K x)) =
    IdeleClassGroup.mk (k := k) (K := K) a
  have hp : IdeleClassGroup.mk (k := k) (K := K) (principalIdele k K x) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
  rw [map_mul, map_div, map_div, hp, div_one]
  exact mul_div_cancel
    (IdeleClassGroup.mk (k := k) (K := K) b) (IdeleClassGroup.mk (k := k) (K := K) a)

variable (k K) [Finite k] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- One finite set of actual places suffices to represent every idele class. -/
theorem exists_finset_sIdeleClass_surjective :
    ∃ S : Finset (Place k K), Function.Surjective (sIdeleClass S) := by
  obtain ⟨S, hS⟩ := exists_finset_picard_representatives k K
  exact ⟨S, sIdeleClass_surjective_of_picard S hS⟩

/-- The representative set may contain prescribed places and be stable under a finite action. -/
theorem exists_finset_stable_sIdeleClass_surjective {G : Type*} [Group G] [Finite G]
    (ρ : G →* SemilinearAut k K) (T : Finset (Place k K)) :
    ∃ S : Finset (Place k K), T ⊆ S ∧
      (∀ g : G, ∀ v : Place k K, ρ g • v ∈ S ↔ v ∈ S) ∧
      Function.Surjective (sIdeleClass S) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨S₀, hS₀⟩ := exists_finset_sIdeleClass_surjective k K
  let S := Finset.univ.biUnion fun g : G => (S₀ ∪ T).image fun v => ρ g • v
  have hinc : S₀ ∪ T ⊆ S := by
    intro v hv
    apply Finset.mem_biUnion.mpr
    refine ⟨1, Finset.mem_univ _, Finset.mem_image.mpr ⟨v, hv, ?_⟩⟩
    rw [map_one, one_smul]
  have hstable : ∀ g : G, ∀ v : Place k K, v ∈ S → ρ g • v ∈ S := by
    intro g v hv
    obtain ⟨h, _, hh⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hh
    apply Finset.mem_biUnion.mpr
    refine ⟨g * h, Finset.mem_univ _, Finset.mem_image.mpr ⟨w, hw, ?_⟩⟩
    rw [map_mul, mul_smul]
  refine ⟨S, fun v hv => hinc (Finset.mem_union_right _ hv), ?_, ?_⟩
  · intro g v
    refine ⟨fun hv => ?_, hstable g v⟩
    have h := hstable g⁻¹ (ρ g • v) hv
    rwa [map_inv, inv_smul_smul] at h
  · intro c
    obtain ⟨a, ha⟩ := hS₀ c
    exact ⟨⟨a.val, sIdeles_mono (fun v hv => hinc (Finset.mem_union_left _ hv)) a.2⟩, ha⟩

end FunctionField.IdeleGroup

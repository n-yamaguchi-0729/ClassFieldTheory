/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Basic
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Constants
public import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.FiniteDimensionalLSpaceZero
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Topology.Separation.Hausdorff
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve

/-!
# Integral functions and arbitrarily deep ray congruences

Globally integral principal ideles form a finite group over a finite
constant field. An integral idele in a ray subgroup differs, to the
prescribed depth at every place, from one of these actual global functions.
If a fixed local component admits these congruences at every depth, it is
the completion value of a single globally integral function.

The local unit group itself is infinite. These two facts distinguish full
local Artin images and retain all principal units, in every characteristic.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve

namespace FunctionField.RayClass

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
  [HasPrincipalDivisors k K]

/-- Functions whose original principal idele is a unit at every place. -/
def integralFunctionUnits : Subgroup Kˣ :=
  IdeleGroup.integralSubgroup.comap (IdeleGroup.principalIdele k K)

/-- The actual completion values of the globally integral function units. -/
def localIntegralFunctionUnits (v : Place k K) : Subgroup v.adicCompletionˣ :=
  (integralFunctionUnits (k := k) (K := K)).map
    (Units.map (algebraMap K v.adicCompletion).toMonoidHom)

/-- An integral idele in a ray class subgroup differs from a globally
integral principal idele by the actual prescribed local higher units. -/
theorem exists_integralFunction_of_rayClass_mem
    (m : Modulus k K) (a : IdeleGroup k K)
    (ha : a ∈ IdeleGroup.integralSubgroup)
    (hm : IdeleClassGroup.mk a ∈ rayClassSubgroup m) :
    ∃ x ∈ integralFunctionUnits (k := k) (K := K),
      ∀ v : Place k K,
        a v / Units.map (algebraMap K v.adicCompletion).toMonoidHom x ∈
          localHigherUnitGroup v (m v) := by
  obtain ⟨b, hb, hba⟩ := hm
  have hprincipal : a / b ∈ IdeleGroup.principalSubgroup k K :=
    QuotientGroup.eq_iff_div_mem.mp hba.symm
  obtain ⟨x, hx⟩ := hprincipal
  have hxintegral : x ∈ integralFunctionUnits (k := k) (K := K) := by
    change IdeleGroup.principalIdele k K x ∈ IdeleGroup.integralSubgroup
    rw [hx]
    exact IdeleGroup.integralSubgroup.div_mem ha
      (congruenceSubgroup_le_integralSubgroup m hb)
  refine ⟨x, hxintegral, ?_⟩
  intro v
  have hprod : Units.map (algebraMap K v.adicCompletion).toMonoidHom x * b v = a v :=
    congrArg (IdeleGroup.component v) (eq_div_iff_mul_eq'.mp hx)
  have hquot : a v / Units.map (algebraMap K v.adicCompletion).toMonoidHom x = b v :=
    div_eq_iff_eq_mul.mpr (hprod.symm.trans (mul_comm _ _))
  rw [hquot]
  exact hb v

variable [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K]

/-- Global integral function units are finite. The proof embeds their
original functions in the actual zero-divisor Riemann--Roch space. -/
theorem finite_integralFunctionUnits :
    Finite (integralFunctionUnits (k := k) (K := K)) := by
  have : IsCurveOver k K := FunctionField.isCurveOver k K
  have : Algebra.EssFiniteType k K := FunctionField.essFiniteType k K
  have : Nonempty (Place k K) := FunctionField.nonempty_place k K
  have : FiniteDimensional k (LSpace (0 : Divisor k K)) :=
    finiteDimensional_lSpace_zero k K
  have : Finite (LSpace (0 : Divisor k K)) := Module.finite_of_finite k
  let f : integralFunctionUnits (k := k) (K := K) → LSpace (0 : Divisor k K) :=
    fun x => ⟨((x : Kˣ) : K), by
      apply mem_lSpace_iff_ord.mpr
      right
      intro v
      have hord : v.ord ((x : Kˣ) : K) = 0 :=
        (IdeleGroup.localOrder_algebraMap v (x : Kˣ)).symm.trans
          ((IdeleGroup.localOrder_eq_zero_iff v _).mpr (x.property v))
      simpa only [Finsupp.zero_apply, neg_zero] using hord.ge⟩
  apply Finite.of_injective f
  intro x y hxy
  apply Subtype.ext
  apply Units.ext
  exact congrArg Subtype.val hxy

/-- At each actual completion there are only finitely many global
integral-function values. -/
theorem finite_localIntegralFunctionUnits (v : Place k K) :
    (localIntegralFunctionUnits v : Set v.adicCompletionˣ).Finite := by
  have : Finite (integralFunctionUnits (k := k) (K := K)) := finite_integralFunctionUnits
  change ((Units.map (algebraMap K v.adicCompletion).toMonoidHom) ''
    (integralFunctionUnits (k := k) (K := K) : Set Kˣ)).Finite
  exact (Set.toFinite _).image _

omit [HasPrincipalDivisors k K] in
private theorem mem_finite_of_all_higherUnit_approximations
    (v : Place k K) (S : Set v.adicCompletionˣ) (hS : S.Finite)
    (u : v.adicCompletionˣ)
    (hu : ∀ n : ℕ, ∃ a ∈ S, u / a ∈ localHigherUnitGroup v n) : u ∈ S := by
  classical
  by_contra hnot
  let T : Set v.adicCompletionˣ := (fun a => u / a) '' S
  have hT : T.Finite := hS.image _
  have hone : (1 : v.adicCompletionˣ) ∈ Tᶜ := by
    rintro ⟨a, ha, hua⟩
    have heq : u = a := div_eq_one.mp hua
    apply hnot
    rw [heq]
    exact ha
  let : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
  have : IsNonarchimedeanLocalField v.adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField v
  obtain ⟨n, _, hn⟩ := LocalFieldTheory.exists_fieldPrincipalUnits_subset_of_mem_nhds
    v.adicCompletion Tᶜ (hT.isClosed.isOpen_compl.mem_nhds hone)
  obtain ⟨a, ha, hua⟩ := hu n
  exact hn hua ⟨a, ha, rfl⟩

/-- Arbitrarily deep actual ray congruences force the given local
component to be the value of one globally integral function. -/
theorem mem_localIntegralFunctionUnits_of_all_single_ray
    (a : IdeleGroup k K) (ha : a ∈ IdeleGroup.integralSubgroup)
    (v : Place k K)
    (h : ∀ n : ℕ, IdeleClassGroup.mk a ∈ rayClassSubgroup (Finsupp.single v n)) :
    a v ∈ localIntegralFunctionUnits v := by
  apply mem_finite_of_all_higherUnit_approximations v
    (localIntegralFunctionUnits v) (finite_localIntegralFunctionUnits v) (a v)
  intro n
  obtain ⟨x, hx, hcong⟩ :=
    exists_integralFunction_of_rayClass_mem (Finsupp.single v n) a ha (h n)
  refine ⟨Units.map (algebraMap K v.adicCompletion).toMonoidHom x, ⟨x, hx, rfl⟩, ?_⟩
  simpa only [Finsupp.single_eq_same] using hcong v

private theorem infinite_units_of_discreteValuationRing
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] : Infinite Rˣ := by
  classical
  apply not_finite_iff_infinite.mp
  intro hfinite
  have : Finite Rˣ := hfinite
  have hcover : Set.univ ⊆
      Set.range (Units.val : Rˣ → R) ∪ Set.range (fun u : Rˣ => 1 - (u : R)) := by
    intro r _
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self r with hr | hr
    · exact Or.inl ⟨hr.unit, hr.unit_spec⟩
    · refine Or.inr ⟨hr.unit, ?_⟩
      change 1 - (hr.unit : R) = r
      rw [hr.unit_spec, sub_sub_cancel]
  have hfin : (Set.univ : Set R).Finite :=
    ((Set.finite_range (Units.val : Rˣ → R)).union
      (Set.finite_range (fun u : Rˣ => 1 - (u : R)))).subset hcover
  have : Finite R := Set.finite_univ_iff.mp hfin
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hinj : Function.Injective (fun r : R => π * r) :=
    fun a b hab => mul_left_cancel₀ hπ.ne_zero hab
  obtain ⟨r, hr⟩ := Finite.surjective_of_injective hinj 1
  exact hπ.not_isUnit (isUnit_iff_exists_inv.mpr ⟨r, hr⟩)

omit [HasPrincipalDivisors k K] [Finite k] [Algebra (RatFunc k) K]
  [IsScalarTower k (RatFunc k) K] [FunctionField k K] in
/-- The full local units at every actual place are infinite, including
the principal-unit direction in the residue characteristic. -/
theorem infinite_localHigherUnitGroup_zero (v : Place k K) :
    Infinite (localHigherUnitGroup v 0) := by
  have : Infinite v.adicCompletionIntegersˣ :=
    infinite_units_of_discreteValuationRing v.adicCompletionIntegers
  let f : v.adicCompletionIntegersˣ → localHigherUnitGroup v 0 := fun u =>
    ⟨Units.map v.adicCompletionIntegers.subtype u, by
      rw [localHigherUnitGroup_zero]
      exact ⟨u.val.property, u.inv.property⟩⟩
  apply Infinite.of_injective f
  intro u w huw
  apply Units.ext
  apply Subtype.ext
  exact congrArg (fun z : localHigherUnitGroup v 0 => ((z : v.adicCompletionˣ) :
    v.adicCompletion)) huw

end FunctionField.RayClass

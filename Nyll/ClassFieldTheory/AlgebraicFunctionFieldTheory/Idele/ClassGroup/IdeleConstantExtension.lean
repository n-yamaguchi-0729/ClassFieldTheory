/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantExtension
import Nyll.AlgebraicCurves.Places.Completion
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.ConstantExtension
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Divisor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.PrincipalCore
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Topology
import Nyll.ProCGroups.Topologies.QuotientMaps
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Order.Filter.Cofinite
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Constant-field enlargement on the actual idele groups

Enlarging the algebraic constants inside the same field does not change a
place's valuation subring. Its height-one prime, completed field, valuation,
and integral units are therefore the same objects. Reindexing by the existing
equivalence of places gives a topological group isomorphism of ideles.

It sends a principal idele to the principal idele of the same function, descends
to idele classes, and scales degrees by the constant-field extension degree.
In particular this applies to the actual full constant field `algebraicClosure k K`.
-/

open scoped RestrictedProduct

noncomputable section

namespace FunctionField

open AlgebraicCurve

variable (k C K : Type*) [Field k] [Field C] [Field K]
    [Algebra k C] [Algebra k K] [Algebra C K] [IsScalarTower k C K]
    [Algebra.IsIntegral k C]

namespace IdeleGroup

/-- Reindex the unchanged completed multiplicative groups by enlargement of constants. -/
def constantExtensionHom : IdeleGroup k K →* IdeleGroup C K :=
  RestrictedProduct.mapAlongMonoidHom
    (B₁ := fun v : Place k K => v.adicCompletionIntegers.units)
    (B₂ := fun w : Place C K => w.adicCompletionIntegers.units)
    (fun v : Place k K => v.adicCompletionˣ)
    (fun w : Place C K => w.adicCompletionˣ)
    (Place.constantFieldEquiv k C (F' := K)).symm
    (Place.constantFieldEquiv k C (F' := K)).symm.injective.tendsto_cofinite
    (fun w => MonoidHom.id w.adicCompletionˣ)
    (Filter.Eventually.of_forall fun _ _ hx => hx)

private def constantRestrictionHom : IdeleGroup C K →* IdeleGroup k K :=
  RestrictedProduct.mapAlongMonoidHom
    (B₁ := fun w : Place C K => w.adicCompletionIntegers.units)
    (B₂ := fun v : Place k K => v.adicCompletionIntegers.units)
    (fun w : Place C K => w.adicCompletionˣ)
    (fun v : Place k K => v.adicCompletionˣ)
    (Place.constantFieldEquiv k C (F' := K))
    (Place.constantFieldEquiv k C (F' := K)).injective.tendsto_cofinite
    (fun v => MonoidHom.id v.adicCompletionˣ)
    (Filter.Eventually.of_forall fun _ _ hx => hx)

@[simp]
theorem constantExtensionHom_apply (a : IdeleGroup k K) (w : Place C K) :
    constantExtensionHom k C K a w = a (w.forgetConstants (K := k)) :=
  rfl

/-- Both restricted-product topologies use the same local spaces and integral-unit subgroups. -/
theorem continuous_constantExtensionHom : Continuous (constantExtensionHom k C K) :=
  RestrictedProduct.mapAlong_continuous
    (A₁ := fun v : Place k K =>
      (v.adicCompletionIntegers.units : Set v.adicCompletionˣ))
    (A₂ := fun w : Place C K =>
      (w.adicCompletionIntegers.units : Set w.adicCompletionˣ))
    (fun v : Place k K => v.adicCompletionˣ)
    (fun w : Place C K => w.adicCompletionˣ)
    (Place.constantFieldEquiv k C (F' := K)).symm
    (Place.constantFieldEquiv k C (F' := K)).symm.injective.tendsto_cofinite
    (fun _ x => x) (Filter.Eventually.of_forall fun _ _ hx => hx)
    (fun _ => continuous_id)

private theorem continuous_constantRestrictionHom :
    Continuous (constantRestrictionHom k C K) :=
  RestrictedProduct.mapAlong_continuous
    (A₁ := fun w : Place C K =>
      (w.adicCompletionIntegers.units : Set w.adicCompletionˣ))
    (A₂ := fun v : Place k K =>
      (v.adicCompletionIntegers.units : Set v.adicCompletionˣ))
    (fun w : Place C K => w.adicCompletionˣ)
    (fun v : Place k K => v.adicCompletionˣ)
    (Place.constantFieldEquiv k C (F' := K))
    (Place.constantFieldEquiv k C (F' := K)).injective.tendsto_cofinite
    (fun _ x => x) (Filter.Eventually.of_forall fun _ _ hx => hx)
    (fun _ => continuous_id)

/-- The actual idele group is independent of the chosen algebraic constant subfield. -/
def constantEquiv : IdeleGroup k K ≃ₜ* IdeleGroup C K where
  toFun := constantExtensionHom k C K
  invFun := constantRestrictionHom k C K
  left_inv a := by
    apply IdeleGroup.ext (k := k) (K := K)
    intro v
    cases v
    rfl
  right_inv a := by
    apply IdeleGroup.ext (k := C) (K := K)
    intro w
    cases w
    rfl
  map_mul' := (constantExtensionHom k C K).map_mul
  continuous_toFun := continuous_constantExtensionHom k C K
  continuous_invFun := continuous_constantRestrictionHom k C K

@[simp]
theorem constantEquiv_apply (a : IdeleGroup k K) (w : Place C K) :
    constantEquiv k C K a w = a (w.forgetConstants (K := k)) :=
  rfl

@[simp]
theorem constantEquiv_symm_apply (a : IdeleGroup C K) (v : Place k K) :
    (constantEquiv k C K).symm a v = a (v.extendConstants C) :=
  rfl

/-- The divisor of the transported idele is the existing reindexed curve divisor. -/
theorem divisor_constantEquiv (a : IdeleGroup k K) :
    (divisor (k := C) (K := K) (constantEquiv k C K a)).toAdd =
      divisorConstantEquiv k C K (divisor (k := k) (K := K) a).toAdd := by
  apply Finsupp.ext
  intro w
  rw [divisorConstantEquiv_apply, divisor_apply (k := C) (K := K),
    divisor_apply (k := k) (K := K)]
  rfl

/-- Enlarging constants divides the numerical idele degree by the constant-field degree. -/
theorem degree_constantEquiv (a : IdeleGroup k K) :
    (degree (k := k) (K := K) a).toAdd = (Module.finrank k C : ℤ) *
      (degree (k := C) (K := K) (constantEquiv k C K a)).toAdd := by
  rw [degree_apply (k := k) (K := K), degree_apply (k := C) (K := K),
    divisor_constantEquiv]
  exact degree_divisorConstantEquiv k C K (divisor (k := k) (K := K) a).toAdd

variable [HasPrincipalDivisors k K] [HasPrincipalDivisors C K]

/-- The same nonzero function gives corresponding principal ideles. -/
@[simp]
theorem constantEquiv_principalIdele (x : Kˣ) :
    constantEquiv k C K (principalIdele k K x) = principalIdele C K x := by
  apply IdeleGroup.ext (k := C) (K := K)
  intro w
  rfl

/-- The subgroup of principal ideles is carried onto the actual principal subgroup. -/
theorem map_principalSubgroup_constantEquiv :
    (principalSubgroup k K).map (constantEquiv k C K).toMulEquiv.toMonoidHom =
      principalSubgroup C K := by
  apply Subgroup.ext
  intro a
  constructor
  · intro ha
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp ha
    have hbRange : b ∈ (principalIdele k K).range := hb
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hbRange
    change a ∈ (principalIdele C K).range
    apply MonoidHom.mem_range.mpr
    refine ⟨x, ?_⟩
    calc
      principalIdele C K x = constantEquiv k C K (principalIdele k K x) :=
        (constantEquiv_principalIdele k C K x).symm
      _ = constantEquiv k C K b := congrArg (constantEquiv k C K) hx
      _ = a := hba
  · intro ha
    have haRange : a ∈ (principalIdele C K).range := ha
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp haRange
    apply Subgroup.mem_map.mpr
    refine ⟨principalIdele k K x, ?_, ?_⟩
    · change principalIdele k K x ∈ (principalIdele k K).range
      exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
    · exact (constantEquiv_principalIdele k C K x).trans hx

end IdeleGroup

namespace IdeleClassGroup

variable [HasPrincipalDivisors k K] [HasPrincipalDivisors C K]

/-- Enlarging the constants identifies the actual topological idele class groups. -/
def constantEquiv : IdeleClassGroup k K ≃ₜ* IdeleClassGroup C K :=
  ProCGroups.QuotientGroup.congrₜ
    (IdeleGroup.principalSubgroup k K) (IdeleGroup.principalSubgroup C K)
    (IdeleGroup.constantEquiv k C K) (IdeleGroup.map_principalSubgroup_constantEquiv k C K)

@[simp]
theorem constantEquiv_mk (a : IdeleGroup k K) :
    constantEquiv k C K (mk (k := k) (K := K) a) =
      mk (k := C) (K := K) (IdeleGroup.constantEquiv k C K a) :=
  rfl

/-- Class degrees retain the constant-field scaling factor. -/
theorem degree_constantEquiv (c : IdeleClassGroup k K) :
    (degree (k := k) (K := K) c).toAdd = (Module.finrank k C : ℤ) *
      (degree (k := C) (K := K) (constantEquiv k C K c)).toAdd := by
  obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := K) c
  rw [constantEquiv_mk, degree_mk (k := k) (K := K), degree_mk (k := C) (K := K)]
  exact IdeleGroup.degree_constantEquiv k C K a

variable [Module.Finite k C]

/-- For a finite constant extension, the isomorphism preserves exactly the degree-zero classes. -/
theorem constantEquiv_mem_degreeZero_iff (c : IdeleClassGroup k K) :
    constantEquiv k C K c ∈ degreeZero (k := C) (K := K) ↔
      c ∈ degreeZero (k := k) (K := K) := by
  rw [mem_degreeZero (k := C) (K := K), mem_degreeZero (k := k) (K := K)]
  have hd : (Module.finrank k C : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.mpr (Module.finrank_pos (R := k) (M := C)).ne'
  have hscale := degree_constantEquiv k C K c
  constructor
  · intro h
    apply Multiplicative.ext
    change (degree (k := k) (K := K) c).toAdd = 0
    rw [hscale, h]
    exact mul_zero _
  · intro h
    apply Multiplicative.ext
    change (degree (k := C) (K := K) (constantEquiv k C K c)).toAdd = 0
    have hprod : (Module.finrank k C : ℤ) *
        (degree (k := C) (K := K) (constantEquiv k C K c)).toAdd = 0 := by
      rw [← hscale, h]
      rfl
    exact (mul_eq_zero.mp hprod).resolve_left hd

/-- The degree-zero topological class groups are identified by the same actual isomorphism. -/
def degreeZeroConstantEquiv :
    degreeZero (k := k) (K := K) ≃ₜ* degreeZero (k := C) (K := K) where
  toFun c := ⟨constantEquiv k C K c,
    (constantEquiv_mem_degreeZero_iff k C K c).2 c.2⟩
  invFun c := ⟨(constantEquiv k C K).symm c,
    (constantEquiv_mem_degreeZero_iff k C K ((constantEquiv k C K).symm c)).1 (by
      rw [ContinuousMulEquiv.apply_symm_apply]
      exact c.2)⟩
  left_inv c := Subtype.ext ((constantEquiv k C K).symm_apply_apply c)
  right_inv c := Subtype.ext ((constantEquiv k C K).apply_symm_apply c)
  map_mul' c d := Subtype.ext ((constantEquiv k C K).map_mul c d)
  continuous_toFun :=
    ((constantEquiv k C K).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((constantEquiv k C K).symm.continuous.comp continuous_subtype_val).subtype_mk _

end IdeleClassGroup

end FunctionField

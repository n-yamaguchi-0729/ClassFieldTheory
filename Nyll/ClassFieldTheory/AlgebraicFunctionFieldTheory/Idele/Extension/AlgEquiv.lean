/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.AlgEquiv
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Divisor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.PrincipalCore
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Topology
import Mathlib.Algebra.Group.Action.End
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Order.Filter.Cofinite

/-!
# Semilinear action on function-field ideles and idele classes

An automorphism permutes the actual places and acts by the corresponding
completed field isomorphisms. The existing restricted-product map constructs
the continuous action. Principal ideles are preserved, so the action descends
to idele classes. The normalized divisor and degree maps are compatible.
-/

open scoped RestrictedProduct WithZero

noncomputable section

namespace FunctionField

open AlgebraicCurve

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace IdeleGroup

private theorem localAction_mem_localUnits (g : SemilinearAut k K) (v : Place k K)
    (x : (g⁻¹ • v).adicCompletionˣ) :
    (placeCompletionUnitsEquiv g⁻¹ v).symm x ∈ v.adicCompletionIntegers.units ↔
      x ∈ (g⁻¹ • v).adicCompletionIntegers.units := by
  have h := placeCompletionUnitsEquiv_mem_localUnits_iff g⁻¹ v
    ((placeCompletionUnitsEquiv g⁻¹ v).symm x)
  rw [ContinuousMulEquiv.apply_symm_apply] at h
  exact h.symm

/-- Transport every component along the inverse permutation of places. -/
def semilinearHom (g : SemilinearAut k K) : IdeleGroup k K →* IdeleGroup k K :=
  RestrictedProduct.mapAlongMonoidHom
    (B₁ := fun v : Place k K => v.adicCompletionIntegers.units)
    (B₂ := fun v : Place k K => v.adicCompletionIntegers.units)
    (fun v : Place k K => v.adicCompletionˣ)
    (fun v : Place k K => v.adicCompletionˣ)
    (fun v => g⁻¹ • v) (MulAction.injective g⁻¹).tendsto_cofinite
    (fun v => (placeCompletionUnitsEquiv g⁻¹ v).symm.toMulEquiv.toMonoidHom)
    (Filter.Eventually.of_forall fun v x hx => (localAction_mem_localUnits g v x).2 hx)

@[simp]
theorem semilinearHom_apply (g : SemilinearAut k K) (a : IdeleGroup k K)
    (v : Place k K) :
    semilinearHom g a v = (placeCompletionUnitsEquiv g⁻¹ v).symm (a (g⁻¹ • v)) :=
  rfl

/-- Reindexing by a permutation and continuous local maps is continuous. -/
theorem continuous_semilinearHom (g : SemilinearAut k K) :
    Continuous (semilinearHom g) :=
  RestrictedProduct.mapAlong_continuous
    (A₁ := fun v : Place k K =>
      (v.adicCompletionIntegers.units : Set v.adicCompletionˣ))
    (A₂ := fun v : Place k K =>
      (v.adicCompletionIntegers.units : Set v.adicCompletionˣ))
    (fun v : Place k K => v.adicCompletionˣ)
    (fun v : Place k K => v.adicCompletionˣ)
    (fun v => g⁻¹ • v) (MulAction.injective g⁻¹).tendsto_cofinite
    (fun v => (placeCompletionUnitsEquiv g⁻¹ v).symm)
    (Filter.Eventually.of_forall fun v x hx => (localAction_mem_localUnits g v x).2 hx)
    (fun v => (placeCompletionUnitsEquiv g⁻¹ v).symm.continuous)

/-- The identity automorphism acts as the identity on ideles. -/
theorem semilinearHom_one (a : IdeleGroup k K) :
    semilinearHom (1 : SemilinearAut k K) a = a := by
  apply IdeleGroup.ext
  intro v
  apply Units.ext
  exact placeCompletionRingEquiv_symm_one
    (fun w : Place k K => (a w : w.adicCompletion)) v

/-- Multiplication of automorphisms agrees with composition on every component. -/
theorem semilinearHom_mul (g h : SemilinearAut k K) (a : IdeleGroup k K) :
    semilinearHom (g * h) a = semilinearHom g (semilinearHom h a) := by
  apply IdeleGroup.ext
  intro v
  apply Units.ext
  exact placeCompletionRingEquiv_symm_mul g h
    (fun w : Place k K => (a w : w.adicCompletion)) v

/-- The canonical multiplicative action induced by the actual completed field maps. -/
instance : MulDistribMulAction (SemilinearAut k K) (IdeleGroup k K) where
  smul := fun g a => semilinearHom g a
  one_smul := semilinearHom_one
  mul_smul := semilinearHom_mul
  smul_one g := (semilinearHom g).map_one
  smul_mul g a b := (semilinearHom g).map_mul a b

@[simp]
theorem smul_apply (g : SemilinearAut k K) (a : IdeleGroup k K) (v : Place k K) :
    (g • a) v = (placeCompletionUnitsEquiv g⁻¹ v).symm (a (g⁻¹ • v)) :=
  rfl

/-- Every semilinear automorphism acts by a topological group automorphism. -/
def semilinearEquiv (g : SemilinearAut k K) : IdeleGroup k K ≃ₜ* IdeleGroup k K where
  __ := MulDistribMulAction.toMulEquiv (IdeleGroup k K) g
  continuous_toFun := continuous_semilinearHom g
  continuous_invFun := continuous_semilinearHom g⁻¹

/-- The idele divisor transforms by the established action on curve divisors. -/
theorem divisor_smul (g : SemilinearAut k K) (a : IdeleGroup k K) :
    (divisor (k := k) (K := K) (g • a)).toAdd =
      g • (divisor (k := k) (K := K) a).toAdd := by
  apply Finsupp.ext
  intro v
  rw [SemilinearAut.divisor_smul_apply, divisor_apply (k := k) (K := K),
    divisor_apply (k := k) (K := K)]
  change -WithZero.log (Valued.v ((placeCompletionRingEquiv g⁻¹ v).symm
      (a (g⁻¹ • v) : (g⁻¹ • v).adicCompletion))) =
    -WithZero.log (Valued.v (a (g⁻¹ • v) : (g⁻¹ • v).adicCompletion))
  have hv := valued_placeCompletionRingEquiv g⁻¹ v
    ((placeCompletionRingEquiv g⁻¹ v).symm
      (a (g⁻¹ • v) : (g⁻¹ • v).adicCompletion))
  rw [RingEquiv.apply_symm_apply] at hv
  exact congrArg (fun z : ℤᵐ⁰ => -WithZero.log z) hv.symm

/-- The degree is invariant under semilinear automorphisms. -/
@[simp]
theorem degree_smul (g : SemilinearAut k K) (a : IdeleGroup k K) :
    degree (k := k) (K := K) (g • a) = degree (k := k) (K := K) a := by
  apply Multiplicative.ext
  rw [degree_apply (k := k) (K := K), degree_apply (k := k) (K := K),
    divisor_smul, SemilinearAut.degree_smul]

variable [HasPrincipalDivisors k K]

/-- The action agrees with the original field automorphism on diagonal ideles. -/
theorem smul_principalIdele (g : SemilinearAut k K) (x : Kˣ) :
    g • principalIdele k K x =
      principalIdele k K (Units.mapEquiv (SemilinearAut.toRingAut g).toMulEquiv x) := by
  apply IdeleGroup.ext
  intro v
  apply Units.ext
  change (placeCompletionRingEquiv g⁻¹ v).symm
      (algebraMap K (g⁻¹ • v).adicCompletion (x : K)) =
    algebraMap K v.adicCompletion (SemilinearAut.toRingAut g (x : K))
  rw [placeCompletionRingEquiv_symm_algebraMap, inv_inv, SemilinearAut.smul_def]

/-- Principal ideles form an invariant subgroup. -/
theorem smul_mem_principalSubgroup (g : SemilinearAut k K)
    {a : IdeleGroup k K} (ha : a ∈ principalSubgroup k K) :
    g • a ∈ principalSubgroup k K := by
  obtain ⟨x, rfl⟩ := ha
  exact ⟨Units.mapEquiv (SemilinearAut.toRingAut g).toMulEquiv x,
    (smul_principalIdele g x).symm⟩

end IdeleGroup

namespace IdeleClassGroup

variable [HasPrincipalDivisors k K]

/-- The completed action descends through the actual subgroup of principal ideles. -/
def semilinearHom (g : SemilinearAut k K) :
    IdeleClassGroup k K →* IdeleClassGroup k K :=
  QuotientGroup.map (IdeleGroup.principalSubgroup k K) (IdeleGroup.principalSubgroup k K)
    (IdeleGroup.semilinearHom g)
    (fun _ ha => IdeleGroup.smul_mem_principalSubgroup g ha)

@[simp]
theorem semilinearHom_mk (g : SemilinearAut k K) (a : IdeleGroup k K) :
    semilinearHom g (mk (k := k) (K := K) a) = mk (k := k) (K := K) (g • a) :=
  rfl

/-- The descended action is continuous for the quotient topology. -/
theorem continuous_semilinearHom (g : SemilinearAut k K) :
    Continuous (semilinearHom g) := by
  apply continuous_coinduced_dom.2
  exact QuotientGroup.continuous_mk.comp (IdeleGroup.continuous_semilinearHom g)

/-- Semilinear automorphisms act multiplicatively on the idele class group. -/
instance : MulDistribMulAction (SemilinearAut k K) (IdeleClassGroup k K) where
  smul := fun g c => semilinearHom g c
  one_smul c := by
    obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := K) c
    change semilinearHom (1 : SemilinearAut k K) (mk (k := k) (K := K) a) =
      mk (k := k) (K := K) a
    rw [semilinearHom_mk, one_smul]
  mul_smul g h c := by
    obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := K) c
    change semilinearHom (g * h) (mk (k := k) (K := K) a) =
      semilinearHom g (semilinearHom h (mk (k := k) (K := K) a))
    rw [semilinearHom_mk, semilinearHom_mk, semilinearHom_mk, mul_smul]
  smul_one g := (semilinearHom g).map_one
  smul_mul g c d := (semilinearHom g).map_mul c d

@[simp]
theorem smul_mk (g : SemilinearAut k K) (a : IdeleGroup k K) :
    g • mk (k := k) (K := K) a = mk (k := k) (K := K) (g • a) :=
  rfl

/-- The descended action is a topological group automorphism. -/
def semilinearEquiv (g : SemilinearAut k K) :
    IdeleClassGroup k K ≃ₜ* IdeleClassGroup k K where
  __ := MulDistribMulAction.toMulEquiv (IdeleClassGroup k K) g
  continuous_toFun := continuous_semilinearHom g
  continuous_invFun := continuous_semilinearHom g⁻¹

/-- Semilinear automorphisms preserve the degree of an idele class. -/
@[simp]
theorem degree_smul (g : SemilinearAut k K) (c : IdeleClassGroup k K) :
    degree (k := k) (K := K) (g • c) = degree (k := k) (K := K) c := by
  obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := K) c
  rw [smul_mk, degree_mk (k := k) (K := K), degree_mk (k := k) (K := K),
    IdeleGroup.degree_smul]

end IdeleClassGroup

end FunctionField

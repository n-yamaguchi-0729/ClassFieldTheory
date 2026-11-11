/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayDegree
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayBaseChange
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayEmbedding
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.PrincipalRayKernel
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayBaseChange
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayProduct
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayReciprocity
public import Mathlib.Data.Finsupp.Single
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve

/-!
# Separating actual ray families by orders and one boundary coordinate

If two actual ray-restricted families have the same ray-class image and
the same order at every place, their quotient is an everywhere integral
principal function. Equality at a single positive boundary coordinate
then forces this function to be one.

This removes the ambiguity in extracting individual factors from a
global transfer identity. Actual base change of a one-place family is
supported over that original place, and any other boundary place supplies
an actual anchor outside its whole fibre.
-/

@[expose] public section

universe u v w

noncomputable section

open AlgebraicCurve

namespace FunctionField.RayClass

section PrincipalSeparation

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
    [HasPrincipalDivisors k K] [∀ v : Place k K, v.FiniteResidue]

private theorem principal_eq_one_of_orders_and_anchor
    (m : Modulus k K) (w : Place k K) (hw : m w ≠ 0)
    (x : Kˣ) (horder : ∀ v : Place k K, v.ord (x : K) = 0)
    (hanchor : Units.map (algebraMap K w.adicCompletion) x ∈
      localHigherUnitGroup w (m w)) : x = 1 := by
  classical
  let n : Modulus k K := Finsupp.single w (m w)
  have hn : n ≠ 0 := by
    intro hzero
    apply hw
    have h := congrArg (fun t : Modulus k K => t w) hzero
    simpa only [n, Finsupp.single_eq_same, Finsupp.zero_apply] using h
  apply principalIdele_eq_one_of_mem_congruence n hn x
  intro v
  by_cases hv : v = w
  · subst v
    change Units.map (algebraMap K w.adicCompletion) x ∈
      localHigherUnitGroup w (Finsupp.single w (m w) w)
    rw [Finsupp.single_eq_same]
    exact hanchor
  · change Units.map (algebraMap K v.adicCompletion) x ∈
      localHigherUnitGroup v (Finsupp.single w (m w) v)
    rw [Finsupp.single_eq_of_ne hv, localHigherUnitGroup_zero]
    exact (IdeleGroup.localOrder_eq_zero_iff v _).mp
      ((IdeleGroup.localOrder_algebraMap v x).trans (horder v))

/-- The original ray-class image, all normalized local orders, and one
positive boundary coordinate determine the entire original ray family. -/
theorem restrictedRay_eq_of_rayClass_order_anchor
    (m : Modulus k K) (a b : RayRestrictedProduct m)
    (hclass : restrictedProductToRayClass m a = restrictedProductToRayClass m b)
    (horder : ∀ v : Place k K,
      localRayFactorOrder m v (a v) = localRayFactorOrder m v (b v))
    (w : Place k K) (hw : m w ≠ 0) (hanchor : a w = b w) : a = b := by
  have hker : a / b ∈ (restrictedProductToRayClass m).ker := by
    change restrictedProductToRayClass m (a / b) = 1
    exact ((map_div (restrictedProductToRayClass m) a b).trans
      (congrArg (fun z : RayClassGroup m => z / restrictedProductToRayClass m b)
        hclass)).trans (div_self' _)
  rw [restrictedProductToRayClass_ker] at hker
  obtain ⟨x, hx⟩ := hker
  have hxorder (v : Place k K) : v.ord (x : K) = 0 := by
    have hv := congrArg (fun q : RayRestrictedProduct m =>
      localRayFactorOrder m v (q v)) hx
    change IdeleGroup.localOrder v (Units.map (algebraMap K v.adicCompletion) x) =
      localRayFactorOrder m v (a v / b v) at hv
    have hzero : localRayFactorOrder m v (a v / b v) = 1 :=
      ((map_div (localRayFactorOrder m v) (a v) (b v)).trans
        (congrArg (fun z : Multiplicative ℤ => z / localRayFactorOrder m v (b v))
          (horder v))).trans (div_self' _)
    exact (IdeleGroup.localOrder_algebraMap v x).symm.trans
      (congrArg Multiplicative.toAdd (hv.trans hzero))
  have hxanchor : Units.map (algebraMap K w.adicCompletion) x ∈
      localHigherUnitGroup w (m w) := by
    have hwx := congrArg (fun q : RayRestrictedProduct m => q w) hx
    change QuotientGroup.mk' (localHigherUnitGroup w (m w))
      (Units.map (algebraMap K w.adicCompletion) x) = a w / b w at hwx
    have hzero : a w / b w = 1 :=
      (congrArg (fun z : RayLocalFactor m w => z / b w) hanchor).trans (div_self' _)
    exact (QuotientGroup.eq_one_iff _).mp (hwx.trans hzero)
  have hxone := principal_eq_one_of_orders_and_anchor m w hw x hxorder hxanchor
  have hab : a / b = 1 := by
    rw [← hx, hxone, map_one]
  exact div_eq_one.mp hab

end PrincipalSeparation

section AbsoluteSeparation

variable {k : Type u} {K : Type v} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K]

/-- Equality under original absolute ray reciprocity, matching local
orders, and one actual boundary coordinate force equality before reciprocity. -/
theorem restrictedRay_eq_of_artin_order_anchor
    (m : Modulus k K) (a b : RayRestrictedProduct m)
    (hartin : restrictedProductAbsoluteArtin m a = restrictedProductAbsoluteArtin m b)
    (horder : ∀ v : Place k K,
      localRayFactorOrder m v (a v) = localRayFactorOrder m v (b v))
    (w : Place k K) (hw : m w ≠ 0) (hanchor : a w = b w) : a = b := by
  have hcurve : IsCurveOver k K := FunctionField.isCurveOver k K
  have hres : ∀ v : Place k K, v.FiniteResidue := fun v => ⟨IsCurveOver.finiteResidue v⟩
  apply restrictedRay_eq_of_rayClass_order_anchor m a b _ horder w hw hanchor
  exact (rayClassAbsoluteArtin_injective m) hartin

/-- For families supported in an actual set of places, a positive boundary
outside that set supplies the needed anchor without choosing a local lift. -/
theorem restrictedRay_eq_of_artin_order_support
    (m : Modulus k K) (s : Set (Place k K)) (a b : RayRestrictedProduct m)
    (hartin : restrictedProductAbsoluteArtin m a = restrictedProductAbsoluteArtin m b)
    (horder : ∀ v : Place k K,
      localRayFactorOrder m v (a v) = localRayFactorOrder m v (b v))
    (ha : ∀ v : Place k K, v ∉ s → a v = 1)
    (hb : ∀ v : Place k K, v ∉ s → b v = 1)
    (hboundary : ∃ w : Place k K, w ∉ s ∧ m w ≠ 0) : a = b := by
  obtain ⟨w, hws, hwm⟩ := hboundary
  exact restrictedRay_eq_of_artin_order_anchor m a b hartin horder w hwm
    ((ha w hws).trans (hb w hws).symm)

end AbsoluteSeparation

section ActualBaseChange

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

/-- Actual finite base change of a one-place ray family is trivial at
every place outside the entire original restriction fibre. -/
theorem restrictedRayBaseChange_single_of_restrict_ne
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (v : Place k K) (x : RayLocalFactor m v)
    (w : Place k L) (hw : w.restrict K ≠ v) :
    restrictedRayBaseChange (L := L) m hm (localRayToRestrictedProduct m v x) w = 1 := by
  rw [restrictedRayBaseChange_apply,
    localRayToRestrictedProduct_of_ne m v (w.restrict K) x hw, map_one]

/-- Another original boundary place lifts to a positive boundary outside
the entire fibre supporting the actual base-changed one-place family. -/
theorem exists_boundary_outside_restriction_fibre
    (m : Modulus k K) (v : Place k K)
    (hboundary : ∃ z : Place k K, z ≠ v ∧ m z ≠ 0) :
    ∃ w : Place k L, w.restrict K ≠ v ∧ rayModulusBaseChange L m w ≠ 0 := by
  obtain ⟨z, hzv, hzm⟩ := hboundary
  obtain ⟨w, hw⟩ := Place.exists_restrict_eq (M := L) z
  refine ⟨w, ?_, ?_⟩
  · exact fun h => hzv (hw.symm.trans h)
  · rw [rayModulusBaseChange_apply, hw]
    exact hzm

/-- A different lower boundary lifts to a genuinely different boundary
at every actual upper place. -/
theorem rayModulusBaseChange_other_boundary
    (m : Modulus k K)
    (hboundary : ∀ v : Place k K, ∃ z : Place k K, z ≠ v ∧ m z ≠ 0)
    (w : Place k L) :
    ∃ z : Place k L, z ≠ w ∧ rayModulusBaseChange L m z ≠ 0 := by
  obtain ⟨z, hzw, hzm⟩ := exists_boundary_outside_restriction_fibre
    (L := L) m (w.restrict K) (hboundary (w.restrict K))
  refine ⟨z, ?_, hzm⟩
  intro h
  exact hzw (congrArg (fun t : Place k L => t.restrict K) h)

end ActualBaseChange

section BaseChangeSeparation

variable {k : Type u} {K : Type v} {L : Type w}
    [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L]
    [FunctionField k L] [HasPrincipalDivisors k L]

/-- A family with the actual base-change Artin value and local orders,
supported over the original place, is the literal base-changed family.
The boundary anchor is supplied by an original different boundary place. -/
theorem restrictedRay_eq_baseChange_single_of_artin_order_support
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (v : Place k K) (x : RayLocalFactor m v)
    (b : RayRestrictedProduct (rayModulusBaseChange L m))
    (hartin :
      restrictedProductAbsoluteArtin (rayModulusBaseChange L m) b =
        restrictedProductAbsoluteArtin (rayModulusBaseChange L m)
          (restrictedRayBaseChange (L := L) m hm (localRayToRestrictedProduct m v x)))
    (horder : ∀ w : Place k L,
      localRayFactorOrder (rayModulusBaseChange L m) w (b w) =
        localRayFactorOrder (rayModulusBaseChange L m) w
          (restrictedRayBaseChange (L := L) m hm (localRayToRestrictedProduct m v x) w))
    (hsupport : ∀ w : Place k L, w.restrict K ≠ v → b w = 1)
    (hboundary : ∃ z : Place k K, z ≠ v ∧ m z ≠ 0) :
    b = restrictedRayBaseChange (L := L) m hm (localRayToRestrictedProduct m v x) := by
  obtain ⟨w, hwv, hwm⟩ := exists_boundary_outside_restriction_fibre (L := L) m v hboundary
  exact restrictedRay_eq_of_artin_order_anchor (rayModulusBaseChange L m) b
    (restrictedRayBaseChange (L := L) m hm (localRayToRestrictedProduct m v x))
    hartin horder w hwm
    ((hsupport w hwv).trans
      (restrictedRayBaseChange_single_of_restrict_ne m hm v x w hwv).symm)

end BaseChangeSeparation

end FunctionField.RayClass

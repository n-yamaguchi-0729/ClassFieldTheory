/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Nyll.ClassFieldTheory.Algebra.RestrictedProduct.Valuation
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.RayPowerQuotient
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Divisor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Degree
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Topology

/-!
# Finite ray quotients with prescribed splitting places

Adjoining the images of the full local multiplicative groups at a nonempty
finite set of places to a ray subgroup makes the quotient finite. An actual
order-one local element gives a class of positive degree. The finite
degree-zero ray kernel then makes the quotient torsion, and finite generation
makes it finite. No degree-one place or existence of a class field is assumed.
-/

noncomputable section

namespace FunctionField.RayClass

private theorem finiteIndex_of_finite_degreeKernel
    {G : Type*} [CommGroup G] [Group.FG G]
    (d : G →* Multiplicative ℤ) [Finite d.ker]
    (H : Subgroup G) {x : G} (hx : x ∈ H) (hd : (d x).toAdd ≠ 0) :
    H.FiniteIndex := by
  have hfinite : Finite (G ⧸ H) := by
    apply CommGroup.finite_of_fg_isMulTorsion
    intro c
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H c
    let a : G := g ^ (d x).toAdd / x ^ (d g).toAdd
    have ha : a ∈ d.ker := by
      change d a = 1
      apply Multiplicative.ext
      change (d (g ^ (d x).toAdd / x ^ (d g).toAdd)).toAdd = 0
      rw [map_div, map_zpow, map_zpow, toAdd_div, toAdd_zpow, toAdd_zpow,
        zsmul_eq_mul, zsmul_eq_mul]
      simp only [Int.cast_id, mul_comm, sub_self]
    have hpow : a ^ Nat.card d.ker = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (x := (⟨a, ha⟩ : d.ker)))
    let q : G →* G ⧸ H := QuotientGroup.mk' H
    have hqx : q x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    have hqa : q a = q g ^ (d x).toAdd := by
      change q (g ^ (d x).toAdd / x ^ (d g).toAdd) = _
      rw [map_div, map_zpow, map_zpow, hqx, one_zpow, div_one]
    have heq := congrArg q hpow
    rw [map_pow, hqa, map_one, ← zpow_natCast, ← zpow_mul] at heq
    exact isOfFinOrder_iff_zpow_eq_one.mpr
      ⟨(d x).toAdd * (Nat.card d.ker : ℤ),
        mul_ne_zero hd (Int.natCast_ne_zero.mpr Nat.card_pos.ne'), heq⟩
  exact Subgroup.finiteIndex_of_finite_quotient

variable {k K : Type} [Field k] [Field K] [Algebra k K]
    [AlgebraicCurve.HasPrincipalDivisors k K]

-- Match the canonical quotient dictionary used by the existing ray-power theorem.
local instance : CommGroup (IdeleClassGroup k K) :=
  QuotientGroup.Quotient.commGroup (G := IdeleGroup k K) (IdeleGroup.principalSubgroup k K)

local instance : IsMulCommutative (IdeleClassGroup k K) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

/-- The ray subgroup together with all local multiplicative groups at the
places required to split completely. -/
def splitRaySubgroup (m : Modulus k K) (S : Finset (AlgebraicCurve.Place k K)) :
    Subgroup (IdeleClassGroup k K) :=
  rayClassSubgroup m ⊔ ⨆ v ∈ S,
    ((IdeleClassGroup.mk (k := k) (K := K)).comp (IdeleGroup.placeIdele v)).range

/-- Every one-place class at a prescribed splitting place is killed. -/
theorem placeIdele_mem_splitRaySubgroup (m : Modulus k K)
    (S : Finset (AlgebraicCurve.Place k K)) {v : AlgebraicCurve.Place k K}
    (hv : v ∈ S) (x : v.adicCompletionˣ) :
    IdeleClassGroup.mk (k := k) (K := K) (IdeleGroup.placeIdele v x) ∈
      splitRaySubgroup m S := by
  apply Subgroup.mem_sup_right
  exact Subgroup.mem_iSup_of_mem v (Subgroup.mem_iSup_of_mem hv ⟨x, rfl⟩)

/-- Enlarging the ray subgroup or adding splitting places enlarges this subgroup. -/
theorem splitRaySubgroup_mono {m n : Modulus k K}
    {S T : Finset (AlgebraicCurve.Place k K)} (hmn : m ≤ n) (hST : S ⊆ T) :
    splitRaySubgroup n S ≤ splitRaySubgroup m T := by
  apply sup_le_sup (rayClassSubgroup_antitone hmn)
  apply iSup_le
  intro v
  apply iSup_le
  intro hv
  exact le_iSup_of_le v (le_iSup_of_le (hST hv) le_rfl)

variable [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K]

/-- The prescribed-splitting ray subgroup is open in the usual topology. -/
theorem isOpen_splitRaySubgroup (m : Modulus k K)
    (S : Finset (AlgebraicCurve.Place k K)) :
    IsOpen (splitRaySubgroup m S : Set (IdeleClassGroup k K)) :=
  Subgroup.isOpen_mono le_sup_left (isOpen_rayClassSubgroup m)

/-- A nonempty set of splitting places removes the infinite degree direction,
so the actual prescribed-splitting ray quotient is finite. -/
theorem finiteIndex_splitRaySubgroup (m : Modulus k K)
    (S : Finset (AlgebraicCurve.Place k K)) (hS : S.Nonempty) :
    (splitRaySubgroup m S).FiniteIndex := by
  obtain ⟨v, hv⟩ := hS
  have : AlgebraicCurve.IsCurveOver k K := FunctionField.isCurveOver k K
  have : Module.Finite k v.ResidueField :=
    AlgebraicCurve.IsCurveOver.finite_residueField v
  have hdeg : (v.deg : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.mpr (Module.finrank_pos (R := k) (M := v.ResidueField)).ne'
  let x : v.adicCompletionˣ :=
    RestrictedProduct.DiscreteValuation.chosenLocalOrderSection v.adicCompletion
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective K
        v.heightOneSpectrum) 1
  have hx : (IdeleGroup.localOrder v x).toAdd = 1 :=
    RestrictedProduct.DiscreteValuation.localOrder_chosenLocalOrderSection
      v.adicCompletion _ 1
  let c : IdeleClassGroup k K :=
    IdeleClassGroup.mk (k := k) (K := K) (IdeleGroup.placeIdele v x)
  have hc : c ∈ splitRaySubgroup m S := placeIdele_mem_splitRaySubgroup m S hv x
  let q : IdeleClassGroup k K →* RayClassGroup m :=
    QuotientGroup.mk' (rayClassSubgroup m)
  let J : Subgroup (RayClassGroup m) := (splitRaySubgroup m S).map q
  have : Group.FG (RayClassGroup m) := rayClassGroup_fg m
  have : Finite (degree m).ker := finite_degreeZero m
  have hdc : (degree m (q c)).toAdd ≠ 0 := by
    change (IdeleClassGroup.degree (k := k) (K := K) c).toAdd ≠ 0
    rw [IdeleClassGroup.degree_mk, IdeleGroup.degree_placeIdele, hx, one_mul]
    exact hdeg
  have hqc : q c ∈ J := ⟨c, hc, rfl⟩
  have : J.FiniteIndex :=
    finiteIndex_of_finite_degreeKernel (degree m) J (x := q c) hqc hdc
  have hcomap : J.comap q = splitRaySubgroup m S := by
    change ((splitRaySubgroup m S).map (QuotientGroup.mk' (rayClassSubgroup m))).comap
      (QuotientGroup.mk' (rayClassSubgroup m)) = _
    rw [QuotientGroup.comap_map_mk']
    exact sup_eq_right.mpr le_sup_left
  rw [← hcomap]
  infer_instance

end FunctionField.RayClass

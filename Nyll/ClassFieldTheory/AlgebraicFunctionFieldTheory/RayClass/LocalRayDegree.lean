/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalArtinDegree
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayEmbedding
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayLocalArtin
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalInertia
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.CompactUnits
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Degree
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Topology
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Topology.Algebra.Group.Quotient
public import Nyll.ClassFieldTheory.Algebra.RestrictedProduct.Valuation

/-!
# Integer order and inertia in the original local ray factors

The original normalized order descends to each local ray factor. Its kernel
is the image of the ordinary local units, and over finite constants this
kernel is finite. Thus the ordinary unit classes are exactly the elements
with a positive power equal to one. The same classes map onto the original
residue inertia under every finite local Artin map.

Arithmetic degree also descends through the actual global ray-Artin subgroup.
On the embedded local factor it is the integer order times the original
residue degree over the full constants, with its arithmetic sign fixed.
-/

@[expose] public section

universe u v w

noncomputable section

open AlgebraicCurve ClassFormation LocalClassFieldTheory

namespace FunctionField.RayClass

section LocalFactors

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The original integer order on a single local ray factor. -/
def localRayFactorOrder (m : Modulus k K) (v : Place k K) :
    RayLocalFactor m v →* Multiplicative ℤ :=
  QuotientGroup.lift (localHigherUnitGroup v (m v)) (IdeleGroup.localOrder v) (by
    intro x hx
    apply Multiplicative.ext
    exact (IdeleGroup.localOrder_eq_zero_iff v x).mpr
      (localHigherUnitGroup_le_localUnits v (m v) hx))

/-- Representatives retain their original normalized order. -/
theorem localRayFactorOrder_mk (m : Modulus k K) (v : Place k K)
    (x : v.adicCompletionˣ) :
    localRayFactorOrder m v
        (QuotientGroup.mk' (localHigherUnitGroup v (m v)) x) =
      IdeleGroup.localOrder v x := rfl

/-- Every integer occurs as the order of an actual local ray class. -/
theorem localRayFactorOrder_surjective (m : Modulus k K) (v : Place k K) :
    Function.Surjective (localRayFactorOrder m v) := by
  intro n
  let hval := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective
    K v.heightOneSpectrum
  let x := RestrictedProduct.DiscreteValuation.chosenLocalOrderSection
    v.adicCompletion hval n.toAdd
  refine ⟨QuotientGroup.mk' (localHigherUnitGroup v (m v)) x, ?_⟩
  apply Multiplicative.ext
  exact RestrictedProduct.DiscreteValuation.localOrder_chosenLocalOrderSection
    v.adicCompletion hval n.toAdd

/-- The ordinary local units inside the actual ray factor. -/
def localRayFactorUnits (m : Modulus k K) (v : Place k K) :
    Subgroup (RayLocalFactor m v) :=
  (localHigherUnitGroup v 0).map
    (QuotientGroup.mk' (localHigherUnitGroup v (m v)))

/-- The order-zero classes are precisely the images of ordinary local units. -/
theorem localRayFactorOrder_eq_one_iff (m : Modulus k K) (v : Place k K)
    (a : RayLocalFactor m v) :
    localRayFactorOrder m v a = 1 ↔ a ∈ localRayFactorUnits m v := by
  constructor
  · intro ha
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (localHigherUnitGroup v (m v)) a
    refine ⟨x, ?_, rfl⟩
    rw [localHigherUnitGroup_zero]
    exact (IdeleGroup.localOrder_eq_zero_iff v x).mp
      (congrArg Multiplicative.toAdd ha)
  · rintro ⟨x, hx, rfl⟩
    apply Multiplicative.ext
    exact (IdeleGroup.localOrder_eq_zero_iff v x).mpr
      (localHigherUnitGroup_le_localUnits v 0 hx)

/-- The local valuation sequence retains exactly the original unit quotient. -/
theorem localRayFactorOrder_ker (m : Modulus k K) (v : Place k K) :
    (localRayFactorOrder m v).ker = localRayFactorUnits m v := by
  apply Subgroup.ext
  intro a
  exact localRayFactorOrder_eq_one_iff m v a

/-- Away from the modulus the local factor is canonically the integer value group. -/
def unramifiedLocalRayFactorEquiv (m : Modulus k K) (v : Place k K)
    (hv : m v = 0) : RayLocalFactor m v ≃* Multiplicative ℤ :=
  MulEquiv.ofBijective (localRayFactorOrder m v)
    ⟨(injective_iff_map_eq_one (localRayFactorOrder m v)).mpr (by
      intro a ha
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (localHigherUnitGroup v (m v)) a
      apply (QuotientGroup.eq_one_iff x).mpr
      rw [hv, localHigherUnitGroup_zero]
      exact (IdeleGroup.localOrder_eq_zero_iff v x).mp
        (congrArg Multiplicative.toAdd ha)), localRayFactorOrder_surjective m v⟩

/-- The unramified identification uses the arithmetic normalized order. -/
theorem unramifiedLocalRayFactorEquiv_mk (m : Modulus k K) (v : Place k K)
    (hv : m v = 0) (x : v.adicCompletionˣ) :
    unramifiedLocalRayFactorEquiv m v hv
        (QuotientGroup.mk' (localHigherUnitGroup v (m v)) x) =
      IdeleGroup.localOrder v x := rfl

variable [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K]

/-- The original local unit image in a ray factor is compact. -/
theorem isCompact_localRayFactorUnits (m : Modulus k K) (v : Place k K) :
    IsCompact (localRayFactorUnits m v : Set (RayLocalFactor m v)) := by
  change IsCompact ((QuotientGroup.mk' (localHigherUnitGroup v (m v))) ''
    (localHigherUnitGroup v 0 : Set v.adicCompletionˣ))
  rw [localHigherUnitGroup_zero]
  exact (FunctionField.isCompact_localUnits v).image QuotientGroup.continuous_mk

/-- At each finite constant stage the ordinary local unit classes form a finite group. -/
theorem finite_localRayFactorUnits (m : Modulus k K) (v : Place k K) :
    Finite (localRayFactorUnits m v) := by
  have : DiscreteTopology (RayLocalFactor m v) :=
    QuotientGroup.discreteTopology (isOpen_localHigherUnitGroup v (m v))
  have : CompactSpace (localRayFactorUnits m v) :=
    isCompact_iff_compactSpace.mp (isCompact_localRayFactorUnits m v)
  exact finite_of_compact_of_discrete

/-- Ordinary units are intrinsic to the local ray group: they are exactly
the classes annihilated by a positive integral power. -/
theorem mem_localRayFactorUnits_iff_exists_pow_eq_one
    (m : Modulus k K) (v : Place k K) (a : RayLocalFactor m v) :
    a ∈ localRayFactorUnits m v ↔ ∃ n : ℕ, n ≠ 0 ∧ a ^ n = 1 := by
  constructor
  · intro ha
    have : Finite (localRayFactorUnits m v) := finite_localRayFactorUnits m v
    refine ⟨Nat.card (localRayFactorUnits m v), Nat.card_pos.ne', ?_⟩
    have hp : (⟨a, ha⟩ : localRayFactorUnits m v) ^
        Nat.card (localRayFactorUnits m v) = 1 := pow_card_eq_one'
    exact congrArg Subtype.val hp
  · rintro ⟨n, hn, ha⟩
    apply (localRayFactorOrder_eq_one_iff m v a).mp
    apply Multiplicative.ext
    have hp := congrArg (fun x : RayLocalFactor m v =>
      (localRayFactorOrder m v x).toAdd) ha
    have hmul : (n : ℤ) * (localRayFactorOrder m v a).toAdd = 0 := by
      simpa only [map_pow, toAdd_pow, nsmul_eq_mul, map_one, toAdd_one] using hp
    exact (mul_eq_zero.mp hmul).resolve_left (Int.natCast_ne_zero.mpr hn)

end LocalFactors

section ArithmeticDegree

variable {k : Type u} {K : Type v} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K]

/-- The actual ray-Artin subgroup has trivial arithmetic constant degree. -/
theorem artinRaySubgroup_le_absoluteAbelianDegree_ker (m : Modulus k K) :
    artinRaySubgroup m ≤ (absoluteAbelianDegree k K).toMonoidHom.ker := by
  rintro a ⟨c, hc, rfl⟩
  have hzero : IdeleClassGroup.normalizedDegree (k := k) (K := K) c = 1 :=
    (IdeleClassGroup.normalizedDegree_eq_one_iff c).mpr
      (rayClassSubgroup_le_degreeZero m hc)
  change absoluteAbelianDegree k K (absoluteArtin k K c) = 1
  rw [absoluteAbelianDegree_artin, hzero, toAdd_one, Int.cast_zero, ofAdd_zero]

/-- The original arithmetic degree on the actual global ray-Artin quotient. -/
def rayAbelianDegree (m : Modulus k K) :
    localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m →* ZHatMul :=
  QuotientGroup.lift (artinRaySubgroup m) (absoluteAbelianDegree k K).toMonoidHom
    (artinRaySubgroup_le_absoluteAbelianDegree_ker m)

/-- Passing to the ray quotient keeps the original arithmetic degree. -/
theorem rayAbelianDegree_mk (m : Modulus k K) (a : localAbsoluteAbelianProfinite K) :
    rayAbelianDegree m (QuotientGroup.mk' (artinRaySubgroup m) a) =
      absoluteAbelianDegree k K a := rfl

/-- Descended arithmetic degree is continuous for the original quotient topology. -/
theorem continuous_rayAbelianDegree (m : Modulus k K) :
    Continuous (rayAbelianDegree m) := by
  rw [← (QuotientGroup.isOpenQuotientMap_mk
    (N := artinRaySubgroup m)).continuous_comp_iff]
  exact (absoluteAbelianDegree k K).continuous_toFun

/-- The embedded local factor has the original normalized integer order
times its actual degree over the full constant field. -/
theorem rayAbelianDegree_localRayAbsoluteArtin (m : Modulus k K) (v : Place k K)
    (a : RayLocalFactor m v) :
    rayAbelianDegree m (localRayAbsoluteArtin m v a) =
      Multiplicative.ofAdd
        (((localRayFactorOrder m v a).toAdd *
          (v.extendConstants (algebraicClosure k K)).deg : ℤ) : ZHat) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (localHigherUnitGroup v (m v)) a
  rw [localRayAbsoluteArtin_mk, rayAbelianDegree_mk, localRayFactorOrder_mk]
  exact absoluteAbelianDegree_placeIdele v x

/-- The original ray-Artin degree determines the local integer order uniquely. -/
theorem rayAbelianDegree_localRayAbsoluteArtin_eq_iff
    (m : Modulus k K) (v : Place k K) (a : RayLocalFactor m v) (n : ℤ) :
    rayAbelianDegree m (localRayAbsoluteArtin m v a) =
        Multiplicative.ofAdd
          ((n * (v.extendConstants (algebraicClosure k K)).deg : ℤ) : ZHat) ↔
      (localRayFactorOrder m v a).toAdd = n := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (localHigherUnitGroup v (m v)) a
  rw [localRayAbsoluteArtin_mk, rayAbelianDegree_mk, localRayFactorOrder_mk]
  exact absoluteAbelianDegree_placeIdele_eq_iff v x n

/-- The arithmetic kernel on an embedded local ray factor is exactly its
ordinary unit subgroup. -/
theorem rayAbelianDegree_localRayAbsoluteArtin_eq_one_iff
    (m : Modulus k K) (v : Place k K) (a : RayLocalFactor m v) :
    rayAbelianDegree m (localRayAbsoluteArtin m v a) = 1 ↔
      a ∈ localRayFactorUnits m v := by
  have h := rayAbelianDegree_localRayAbsoluteArtin_eq_iff m v a 0
  have hzero : (localRayFactorOrder m v a).toAdd = 0 ↔
      localRayFactorOrder m v a = 1 :=
    ⟨Multiplicative.ext, fun h => congrArg Multiplicative.toAdd h⟩
  have hdegree : rayAbelianDegree m (localRayAbsoluteArtin m v a) = 1 ↔
      (localRayFactorOrder m v a).toAdd = 0 := by
    simpa only [zero_mul, Int.cast_zero, ofAdd_zero] using h
  exact hdegree.trans (hzero.trans (localRayFactorOrder_eq_one_iff m v a))

end ArithmeticDegree

section FiniteInertia

variable {k : Type u} {K : Type v} {L : Type w}
    [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- The intrinsic finite-order part of a local ray factor maps onto the
original inertia kernel under the original finite local Artin map. -/
theorem localRayDecompositionArtin_units_eq_residue_ker
    (m : Modulus k K)
    (hm : extensionConductor (k := k) (K := K) (L := L) ≤ m) (w : Place k L) :
    (localRayFactorUnits m (w.restrict K)).map (localRayDecompositionArtin m hm w) =
      (IdeleGroup.decompositionResidueAut (K := K) w).ker := by
  have hcomp : (localRayDecompositionArtin m hm w).comp
      (QuotientGroup.mk' (localHigherUnitGroup (w.restrict K) (m (w.restrict K)))) =
        (localDecompositionArtin (K := K) w).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    exact localRayDecompositionArtin_mk m hm w x
  rw [localRayFactorUnits, Subgroup.map_map, hcomp]
  exact localDecompositionArtin_units_eq_residue_ker (K := K) w

end FiniteInertia

end FunctionField.RayClass

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayDegree
public import Nyll.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Separation
public import Nyll.ProCGroups.ProC.Quotients.ClosedNormal
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Algebra.Monoid
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic

/-!
# Recovering the discrete local Artin image inside its profinite closure

The original local ray factor has compact unit kernel and surjective integer
order. Its arithmetic degree is that order times the actual residue degree.
Consequently its image in the original ray-Artin quotient consists exactly
of the elements of its closure with an integral local Frobenius degree.

The topological step is proved using the actual finite open-normal
quotients: the degree is injective on the closure of a cyclic subgroup
whose generator has positive integral degree. No local multiplicative
equivalence or decomposition comparison is an input to this result.
-/

@[expose] public section

universe u v

noncomputable section

open AlgebraicCurve ClassFormation LocalClassFieldTheory
open scoped Pointwise Topology

namespace FunctionField.RayClass

section ProfiniteClosure

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
private theorem profiniteDegree_zpow
    (degree : G →ₜ* Multiplicative ZHat) (t : G) (d : ℕ)
    (ht : degree t = Multiplicative.ofAdd (d : ZHat)) (n : ℤ) :
    degree (t ^ n) = Multiplicative.ofAdd ((n * (d : ℤ) : ℤ) : ZHat) := by
  rw [map_zpow, ht]
  apply Multiplicative.ext
  change n • (d : ZHat) = ((n * (d : ℤ) : ℤ) : ZHat)
  rw [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast]

private theorem cyclicClosure_eq_one_of_degree_eq_one
    (degree : G →ₜ* Multiplicative ZHat) (t : G) (d : ℕ) (hd : 0 < d)
    (ht : degree t = Multiplicative.ofAdd (d : ZHat))
    (x : G) (hx : x ∈ (Subgroup.zpowers t).topologicalClosure)
    (hdegree : degree x = 1) : x = 1 := by
  apply ProCGroups.ProC.OpenNormalSubgroup.eq_of_forall_quotientProj_eq
  intro U
  let q := ProCGroups.ProC.OpenNormalSubgroup.quotientProj U
  let n : ℕ := Nat.card (G ⧸ (U : Subgroup G))
  have hn : 0 < n := Nat.card_pos
  have hqpow : q t ^ n = 1 := pow_card_eq_one'
  let c : ℕ := d * n
  have hc : 0 < c := Nat.mul_pos hd hn
  let reduction : G → ZMod c :=
    fun g => zHatReduction c hc (degree g).toAdd
  have hcontinuous : Continuous reduction :=
    (zHatReduction c hc).continuous_toFun.comp
      (continuous_toAdd.comp degree.continuous_toFun)
  let O : Set G := q ⁻¹' {q x} ∩ reduction ⁻¹' {0}
  have hOopen : IsOpen O :=
    ((isOpen_discrete ({q x} : Set (G ⧸ (U : Subgroup G)))).preimage
      q.continuous_toFun).inter
      ((isOpen_discrete ({0} : Set (ZMod c))).preimage hcontinuous)
  have hxO : x ∈ O := by
    refine ⟨rfl, ?_⟩
    change zHatReduction c hc (degree x).toAdd = 0
    rw [hdegree]
    exact map_zero (zHatReduction c hc)
  have hxclosure : x ∈ closure (Subgroup.zpowers t : Set G) := hx
  obtain ⟨y, hyO, hy⟩ := mem_closure_iff.mp hxclosure O hOopen hxO
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hmod : ((a * (d : ℤ) : ℤ) : ZMod c) = 0 := by
    have hyzero : zHatReduction c hc (degree y).toAdd = 0 := hyO.2
    rw [← ha, profiniteDegree_zpow degree t d ht a] at hyzero
    exact (zHatReduction_intCast c hc (a * (d : ℤ))).symm.trans hyzero
  have hdiv : (c : ℤ) ∣ a * (d : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (a * (d : ℤ)) c).mp hmod
  obtain ⟨b, hb⟩ := hdiv
  have haeq : a = (n : ℤ) * b := by
    apply mul_left_cancel₀ (Int.natCast_ne_zero.mpr hd.ne')
    calc
      (d : ℤ) * a = a * (d : ℤ) := mul_comm _ _
      _ = (c : ℤ) * b := hb
      _ = (d : ℤ) * ((n : ℤ) * b) := by
        change ((d * n : ℕ) : ℤ) * b = (d : ℤ) * ((n : ℤ) * b)
        rw [Nat.cast_mul, mul_assoc]
  have hqy : q y = 1 := by
    rw [← ha, map_zpow, haeq, zpow_mul, zpow_natCast, hqpow, one_zpow]
  have hqx : q x = 1 := hyO.1.symm.trans hqy
  exact hqx.trans (map_one q).symm

private theorem cyclicClosure_eq_zpow_of_degree_eq
    (degree : G →ₜ* Multiplicative ZHat) (t : G) (d : ℕ) (hd : 0 < d)
    (ht : degree t = Multiplicative.ofAdd (d : ZHat))
    (x : G) (hx : x ∈ (Subgroup.zpowers t).topologicalClosure)
    (n : ℤ) (hdegree : degree x = degree (t ^ n)) : x = t ^ n := by
  have hn : t ^ n ∈ (Subgroup.zpowers t).topologicalClosure :=
    Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩)
  apply div_eq_one.mp
  apply cyclicClosure_eq_one_of_degree_eq_one degree t d hd ht
    (x / t ^ n) ((Subgroup.zpowers t).topologicalClosure.div_mem hx hn)
  rw [map_div, hdegree, div_self']

private theorem mem_range_iff_mem_closure_and_integral_degree
    {A : Type*} [Group A] (f : A →* G) (order : A →* Multiplicative ℤ)
    (hsurj : Function.Surjective order)
    (degree : G →ₜ* Multiplicative ZHat) (d : ℕ) (hd : 0 < d)
    (hdegree : ∀ a, degree (f a) =
      Multiplicative.ofAdd (((order a).toAdd * (d : ℤ) : ℤ) : ZHat))
    (hcompact : IsCompact ((order.ker.map f : Subgroup G) : Set G)) (g : G) :
    g ∈ f.range ↔ g ∈ f.range.topologicalClosure ∧
      ∃ n : ℤ, degree g = Multiplicative.ofAdd ((n * (d : ℤ) : ℤ) : ZHat) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨Subgroup.le_topologicalClosure _ ⟨a, rfl⟩,
      (order a).toAdd, hdegree a⟩
  · rintro ⟨hg, n, hn⟩
    obtain ⟨a₀, ha₀⟩ := hsurj (Multiplicative.ofAdd (1 : ℤ))
    let t : G := f a₀
    let C : Subgroup G := (Subgroup.zpowers t).topologicalClosure
    let V : Subgroup G := order.ker.map f
    have ht : degree t = Multiplicative.ofAdd (d : ZHat) := by
      change degree (f a₀) = Multiplicative.ofAdd (d : ZHat)
      rw [hdegree, ha₀]
      change Multiplicative.ofAdd (((1 : ℤ) * (d : ℤ) : ℤ) : ZHat) =
        Multiplicative.ofAdd (d : ZHat)
      rw [one_mul, Int.cast_natCast]
    have hCcompact : IsCompact (C : Set G) :=
      (Subgroup.isClosed_topologicalClosure (Subgroup.zpowers t)).isCompact
    have hproductClosed : IsClosed ((V : Set G) * (C : Set G)) :=
      (hcompact.mul hCcompact).isClosed
    have hsubset : (f.range : Set G) ⊆ (V : Set G) * (C : Set G) := by
      rintro _ ⟨a, rfl⟩
      let e : ℤ := (order a).toAdd
      let b : A := a / a₀ ^ e
      have horderPow : order (a₀ ^ e) = order a := by
        rw [map_zpow, ha₀]
        apply Multiplicative.ext
        change e • (1 : ℤ) = (order a).toAdd
        rw [zsmul_eq_mul, mul_one]
        rfl
      have hb : b ∈ order.ker := by
        change order (a / a₀ ^ e) = 1
        rw [map_div, horderPow, div_self']
      have he : t ^ e ∈ C :=
        Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers_iff.mpr ⟨e, rfl⟩)
      refine ⟨f b, ⟨b, hb, rfl⟩, t ^ e, he, ?_⟩
      change f (a / a₀ ^ e) * f a₀ ^ e = f a
      rw [map_div, map_zpow, div_mul_cancel]
    have hgproduct : g ∈ (V : Set G) * (C : Set G) :=
      (closure_minimal hsubset hproductClosed) hg
    obtain ⟨u, hu, z, hz, huz⟩ := hgproduct
    obtain ⟨b, hb, rfl⟩ := hu
    have hbdegree : degree (f b) = 1 := by
      rw [hdegree, show order b = 1 from hb]
      change Multiplicative.ofAdd (((0 : ℤ) * (d : ℤ) : ℤ) : ZHat) = 1
      rw [zero_mul, Int.cast_zero]
      rfl
    have hzdegree : degree z = degree (t ^ n) := by
      rw [profiniteDegree_zpow degree t d ht n]
      calc
        degree z = degree (f b * z) := by rw [map_mul, hbdegree, one_mul]
        _ = degree g := congrArg degree huz
        _ = Multiplicative.ofAdd ((n * (d : ℤ) : ℤ) : ZHat) := hn
    have hzeq : z = t ^ n :=
      cyclicClosure_eq_zpow_of_degree_eq degree t d hd ht z hz n hzdegree
    refine ⟨b * a₀ ^ n, ?_⟩
    rw [map_mul, map_zpow]
    change f b * t ^ n = g
    rw [← hzeq]
    exact huz

end ProfiniteClosure

section LocalRayImage

variable {k : Type u} {K : Type v} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K]

omit [HasPrincipalDivisors k K] in
/-- Every original place has positive residue degree over the full constants. -/
theorem fullConstant_placeDegree_pos (v : Place k K) :
    0 < (v.extendConstants (algebraicClosure k K)).deg := by
  have : IsCurveOver (algebraicClosure k K) K := isCurveOver_fullConstants k K
  have : Module.Finite (algebraicClosure k K)
      (v.extendConstants (algebraicClosure k K)).ResidueField :=
    IsCurveOver.finiteResidue _
  exact Module.finrank_pos

/-- Reduction modulo the original residue degree kills the arithmetic
degree of the entire closed local Artin image. -/
theorem localRayClosure_degree_reduction_eq_zero
    (m : Modulus k K) (v : Place k K)
    (g : localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m)
    (hg : g ∈ (localRayAbsoluteArtin m v).range.topologicalClosure) :
    zHatReduction (v.extendConstants (algebraicClosure k K)).deg
      (fullConstant_placeDegree_pos v) (rayAbelianDegree m g).toAdd = 0 := by
  let d : ℕ := (v.extendConstants (algebraicClosure k K)).deg
  let reduction : (localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m) → ZMod d :=
    fun a => zHatReduction d (fullConstant_placeDegree_pos v)
      (rayAbelianDegree m a).toAdd
  have hcontinuous : Continuous reduction :=
    (zHatReduction d (fullConstant_placeDegree_pos v)).continuous_toFun.comp
      (continuous_toAdd.comp (continuous_rayAbelianDegree m))
  have hclosed : IsClosed {a | reduction a = 0} :=
    isClosed_eq hcontinuous continuous_const
  have hsubset : ((localRayAbsoluteArtin m v).range :
      Set (localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m)) ⊆
        {a | reduction a = 0} := by
    rintro _ ⟨a, rfl⟩
    change zHatReduction d (fullConstant_placeDegree_pos v)
      (rayAbelianDegree m (localRayAbsoluteArtin m v a)).toAdd = 0
    rw [rayAbelianDegree_localRayAbsoluteArtin]
    change zHatReduction d (fullConstant_placeDegree_pos v)
      (((localRayFactorOrder m v a).toAdd * (d : ℤ) : ℤ) : ZHat) = 0
    rw [zHatReduction_intCast]
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((localRayFactorOrder m v a).toAdd * (d : ℤ)) d).mpr
    exact ⟨(localRayFactorOrder m v a).toAdd, mul_comm _ _⟩
  exact (closure_minimal hsubset hclosed) hg

/-- An integral arithmetic degree occurring in the closed local image is
divisible by the actual degree of the original place. -/
theorem fullConstant_placeDegree_dvd_of_mem_localRayClosure
    (m : Modulus k K) (v : Place k K)
    (g : localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m)
    (hg : g ∈ (localRayAbsoluteArtin m v).range.topologicalClosure)
    (n : ℕ) (hdegree : rayAbelianDegree m g = Multiplicative.ofAdd (n : ZHat)) :
    (v.extendConstants (algebraicClosure k K)).deg ∣ n := by
  let d : ℕ := (v.extendConstants (algebraicClosure k K)).deg
  have hred : zHatReduction d (fullConstant_placeDegree_pos v) (n : ZHat) =
      (n : ZMod d) := by
    simpa only [Int.cast_natCast] using
      zHatReduction_intCast d (fullConstant_placeDegree_pos v) (n : ℤ)
  have hz : zHatReduction d (fullConstant_placeDegree_pos v) (n : ZHat) = 0 := by
    have h := localRayClosure_degree_reduction_eq_zero m v g hg
    rw [hdegree] at h
    exact h
  exact (ZMod.natCast_eq_zero_iff n d).mp (hred.symm.trans hz)

/-- The discrete original local ray image is recovered from its profinite
closure by requiring an integral power of the actual residue Frobenius. -/
theorem mem_localRayAbsoluteArtin_range_iff (m : Modulus k K) (v : Place k K)
    (g : localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m) :
    g ∈ (localRayAbsoluteArtin m v).range ↔
      g ∈ (localRayAbsoluteArtin m v).range.topologicalClosure ∧
        ∃ n : ℤ, rayAbelianDegree m g = Multiplicative.ofAdd
          ((n * (v.extendConstants (algebraicClosure k K)).deg : ℤ) : ZHat) := by
  have : IsClosed (artinRaySubgroup m : Set (localAbsoluteAbelianProfinite K)) :=
    isClosed_artinRaySubgroup m
  have : TotallyDisconnectedSpace
      (localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m) :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (artinRaySubgroup m) (isClosed_artinRaySubgroup m)
  have : DiscreteTopology (RayLocalFactor m v) :=
    QuotientGroup.discreteTopology (isOpen_localHigherUnitGroup v (m v))
  have hcontinuous : Continuous (localRayAbsoluteArtin m v) :=
    continuous_of_discreteTopology
  have hcompact : IsCompact
      (((localRayFactorOrder m v).ker.map (localRayAbsoluteArtin m v) :
        Subgroup (localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m)) :
        Set (localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m)) := by
    rw [localRayFactorOrder_ker]
    exact (isCompact_localRayFactorUnits m v).image hcontinuous
  let degree : (localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m) →ₜ*
      Multiplicative ZHat :=
    { toMonoidHom := rayAbelianDegree m
      continuous_toFun := continuous_rayAbelianDegree m }
  exact mem_range_iff_mem_closure_and_integral_degree
    (localRayAbsoluteArtin m v) (localRayFactorOrder m v)
    (localRayFactorOrder_surjective m v) degree
    (v.extendConstants (algebraicClosure k K)).deg (fullConstant_placeDegree_pos v)
    (rayAbelianDegree_localRayAbsoluteArtin m v) hcompact g

end LocalRayImage

end FunctionField.RayClass

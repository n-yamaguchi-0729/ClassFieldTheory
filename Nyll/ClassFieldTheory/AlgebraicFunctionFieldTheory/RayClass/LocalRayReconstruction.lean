/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayClosure
public import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Local multiplicative reconstruction from the original Artin quotients

An equivalence of the original ray-Artin quotients preserving the closed
local images and arithmetic degree determines the original residue degrees
and preserves their discrete local images. When each modulus has a nonzero
component away from the distinguished place, the original local embeddings therefore produce
a unique multiplicative equivalence of the actual local ray factors.

The constructed equivalence commutes with the original Artin symbols and
preserves the original integer valuations and ordinary unit subgroups.
These are consequences of the quotient comparison, rather than additional
local reconstruction assumptions.
-/

@[expose] public section

universe u v u₁ v₁ u₂ v₂

noncomputable section

open AlgebraicCurve ClassFormation LocalClassFieldTheory

namespace FunctionField.RayClass

section ImageEquivalence

variable {k : Type u} {K : Type v} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K]

/-- The original local ray factor identified with its actual Artin image. -/
def localRayAbsoluteArtinRangeEquiv (m : Modulus k K) (v : Place k K)
    (hm : ∃ w : Place k K, w ≠ v ∧ m w ≠ 0) :
    RayLocalFactor m v ≃* (localRayAbsoluteArtin m v).range :=
  let f : RayLocalFactor m v →* (localRayAbsoluteArtin m v).range :=
    { toFun a := ⟨localRayAbsoluteArtin m v a, ⟨a, rfl⟩⟩
      map_one' := Subtype.ext (map_one (localRayAbsoluteArtin m v))
      map_mul' a b := Subtype.ext (map_mul (localRayAbsoluteArtin m v) a b) }
  MulEquiv.ofBijective f
    ⟨fun _a _b h => localRayAbsoluteArtin_injective m v hm (congrArg Subtype.val h),
      fun ⟨_g, a, ha⟩ => ⟨a, Subtype.ext ha⟩⟩

/-- The range identification retains the original local Artin value. -/
theorem localRayAbsoluteArtinRangeEquiv_apply (m : Modulus k K) (v : Place k K)
    (hm : ∃ w : Place k K, w ≠ v ∧ m w ≠ 0) (a : RayLocalFactor m v) :
    (localRayAbsoluteArtinRangeEquiv m v hm a :
      localAbsoluteAbelianProfinite K ⧸ artinRaySubgroup m) =
        localRayAbsoluteArtin m v a := rfl

/-- Inverting the range identification recovers the original local symbol. -/
theorem localRayAbsoluteArtinRangeEquiv_symm_apply
    (m : Modulus k K) (v : Place k K)
    (hm : ∃ w : Place k K, w ≠ v ∧ m w ≠ 0)
    (a : (localRayAbsoluteArtin m v).range) :
    localRayAbsoluteArtin m v ((localRayAbsoluteArtinRangeEquiv m v hm).symm a) = a :=
  congrArg Subtype.val ((localRayAbsoluteArtinRangeEquiv m v hm).apply_symm_apply a)

end ImageEquivalence

section Comparison

variable {k₁ : Type u₁} {K₁ : Type v₁} {k₂ : Type u₂} {K₂ : Type v₂}
    [Field k₁] [Finite k₁] [Field K₁] [Algebra k₁ K₁]
    [Algebra (RatFunc k₁) K₁] [IsScalarTower k₁ (RatFunc k₁) K₁]
    [FunctionField k₁ K₁] [HasPrincipalDivisors k₁ K₁]
    [Field k₂] [Finite k₂] [Field K₂] [Algebra k₂ K₂]
    [Algebra (RatFunc k₂) K₂] [IsScalarTower k₂ (RatFunc k₂) K₂]
    [FunctionField k₂ K₂] [HasPrincipalDivisors k₂ K₂]

variable (m₁ : Modulus k₁ K₁) (v₁ : Place k₁ K₁)
    (m₂ : Modulus k₂ K₂) (v₂ : Place k₂ K₂)
    (e : (localAbsoluteAbelianProfinite K₁ ⧸ artinRaySubgroup m₁) ≃*
      (localAbsoluteAbelianProfinite K₂ ⧸ artinRaySubgroup m₂))
    (hclosure : ∀ g, g ∈ (localRayAbsoluteArtin m₁ v₁).range.topologicalClosure ↔
      e g ∈ (localRayAbsoluteArtin m₂ v₂).range.topologicalClosure)
    (hdegree : ∀ g, rayAbelianDegree m₂ (e g) = rayAbelianDegree m₁ g)

include hclosure hdegree in
/-- Closed local image and arithmetic degree preservation determine the
actual residue degree over the full constants on both sides. -/
theorem fullConstant_placeDegree_eq_of_artinComparison :
    (v₁.extendConstants (algebraicClosure k₁ K₁)).deg =
      (v₂.extendConstants (algebraicClosure k₂ K₂)).deg := by
  obtain ⟨a, ha⟩ :=
    localRayFactorOrder_surjective m₁ v₁ (Multiplicative.ofAdd (1 : ℤ))
  obtain ⟨b, hb⟩ :=
    localRayFactorOrder_surjective m₂ v₂ (Multiplicative.ofAdd (1 : ℤ))
  have haDegree : rayAbelianDegree m₁ (localRayAbsoluteArtin m₁ v₁ a) =
      Multiplicative.ofAdd ((v₁.extendConstants (algebraicClosure k₁ K₁)).deg : ZHat) := by
    rw [rayAbelianDegree_localRayAbsoluteArtin, ha]
    change Multiplicative.ofAdd
      (((1 : ℤ) * (v₁.extendConstants (algebraicClosure k₁ K₁)).deg : ℤ) : ZHat) = _
    rw [one_mul, Int.cast_natCast]
  have hbDegree : rayAbelianDegree m₂ (localRayAbsoluteArtin m₂ v₂ b) =
      Multiplicative.ofAdd ((v₂.extendConstants (algebraicClosure k₂ K₂)).deg : ZHat) := by
    rw [rayAbelianDegree_localRayAbsoluteArtin, hb]
    change Multiplicative.ofAdd
      (((1 : ℤ) * (v₂.extendConstants (algebraicClosure k₂ K₂)).deg : ℤ) : ZHat) = _
    rw [one_mul, Int.cast_natCast]
  have hdiv₂ : (v₂.extendConstants (algebraicClosure k₂ K₂)).deg ∣
      (v₁.extendConstants (algebraicClosure k₁ K₁)).deg := by
    apply fullConstant_placeDegree_dvd_of_mem_localRayClosure m₂ v₂
      (e (localRayAbsoluteArtin m₁ v₁ a))
      ((hclosure (localRayAbsoluteArtin m₁ v₁ a)).mp
        (Subgroup.le_topologicalClosure _ ⟨a, rfl⟩))
    exact (hdegree (localRayAbsoluteArtin m₁ v₁ a)).trans haDegree
  have hdiv₁ : (v₁.extendConstants (algebraicClosure k₁ K₁)).deg ∣
      (v₂.extendConstants (algebraicClosure k₂ K₂)).deg := by
    have hmem : e.symm (localRayAbsoluteArtin m₂ v₂ b) ∈
        (localRayAbsoluteArtin m₁ v₁).range.topologicalClosure := by
      apply (hclosure (e.symm (localRayAbsoluteArtin m₂ v₂ b))).mpr
      rw [e.apply_symm_apply]
      exact Subgroup.le_topologicalClosure _ ⟨b, rfl⟩
    apply fullConstant_placeDegree_dvd_of_mem_localRayClosure m₁ v₁
      (e.symm (localRayAbsoluteArtin m₂ v₂ b)) hmem
    calc
      rayAbelianDegree m₁ (e.symm (localRayAbsoluteArtin m₂ v₂ b)) =
          rayAbelianDegree m₂ (e (e.symm (localRayAbsoluteArtin m₂ v₂ b))) :=
        (hdegree (e.symm (localRayAbsoluteArtin m₂ v₂ b))).symm
      _ = rayAbelianDegree m₂ (localRayAbsoluteArtin m₂ v₂ b) := by
        rw [e.apply_symm_apply]
      _ = Multiplicative.ofAdd
          ((v₂.extendConstants (algebraicClosure k₂ K₂)).deg : ZHat) := hbDegree
  exact Nat.dvd_antisymm hdiv₁ hdiv₂

variable (hplaceDegree : (v₁.extendConstants (algebraicClosure k₁ K₁)).deg =
      (v₂.extendConstants (algebraicClosure k₂ K₂)).deg)

include hclosure hdegree hplaceDegree in
/-- Closed local image and arithmetic degree preservation force preservation
of the actual discrete local Artin image. -/
theorem localRayAbsoluteArtin_range_map_eq :
    (localRayAbsoluteArtin m₁ v₁).range.map e.toMonoidHom =
      (localRayAbsoluteArtin m₂ v₂).range := by
  have hmem (g : localAbsoluteAbelianProfinite K₁ ⧸ artinRaySubgroup m₁) :
      g ∈ (localRayAbsoluteArtin m₁ v₁).range ↔
        e g ∈ (localRayAbsoluteArtin m₂ v₂).range := by
    rw [mem_localRayAbsoluteArtin_range_iff m₁ v₁ g,
      mem_localRayAbsoluteArtin_range_iff m₂ v₂ (e g),
      ← hclosure g, hdegree g, hplaceDegree]
  apply Subgroup.ext
  intro g
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (hmem a).mp ha
  · intro hg
    refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    apply (hmem (e.symm g)).mpr
    rw [e.apply_symm_apply]
    exact hg

variable (hm₁ : ∃ w : Place k₁ K₁, w ≠ v₁ ∧ m₁ w ≠ 0)
    (hm₂ : ∃ w : Place k₂ K₂, w ≠ v₂ ∧ m₂ w ≠ 0)

/-- The local multiplicative equivalence reconstructed from the original
Artin quotient comparison and its closed decomposition images. -/
def localRayEquivOfArtinComparison : RayLocalFactor m₁ v₁ ≃* RayLocalFactor m₂ v₂ :=
  (localRayAbsoluteArtinRangeEquiv m₁ v₁ hm₁).trans
    (((e.subgroupMap (localRayAbsoluteArtin m₁ v₁).range).trans
      (MulEquiv.subgroupCongr
        (localRayAbsoluteArtin_range_map_eq m₁ v₁ m₂ v₂ e
          hclosure hdegree hplaceDegree))).trans
      (localRayAbsoluteArtinRangeEquiv m₂ v₂ hm₂).symm)

/-- The reconstructed map commutes with the original local Artin symbols. -/
theorem localRayEquivOfArtinComparison_artin (a : RayLocalFactor m₁ v₁) :
    localRayAbsoluteArtin m₂ v₂
        (localRayEquivOfArtinComparison m₁ v₁ m₂ v₂ e
          hclosure hdegree hplaceDegree hm₁ hm₂ a) =
      e (localRayAbsoluteArtin m₁ v₁ a) := by
  exact congrArg Subtype.val
    ((localRayAbsoluteArtinRangeEquiv m₂ v₂ hm₂).apply_symm_apply
      ((MulEquiv.subgroupCongr
        (localRayAbsoluteArtin_range_map_eq m₁ v₁ m₂ v₂ e
          hclosure hdegree hplaceDegree))
        ((e.subgroupMap (localRayAbsoluteArtin m₁ v₁).range)
          (localRayAbsoluteArtinRangeEquiv m₁ v₁ hm₁ a))))

/-- Arithmetic degree fixes the sign and scale of the reconstructed integer order. -/
theorem localRayEquivOfArtinComparison_order (a : RayLocalFactor m₁ v₁) :
    localRayFactorOrder m₂ v₂
        (localRayEquivOfArtinComparison m₁ v₁ m₂ v₂ e
          hclosure hdegree hplaceDegree hm₁ hm₂ a) =
      localRayFactorOrder m₁ v₁ a := by
  apply Multiplicative.ext
  apply (rayAbelianDegree_localRayAbsoluteArtin_eq_iff m₂ v₂
    (localRayEquivOfArtinComparison m₁ v₁ m₂ v₂ e
      hclosure hdegree hplaceDegree hm₁ hm₂ a)
    (localRayFactorOrder m₁ v₁ a).toAdd).mp
  rw [localRayEquivOfArtinComparison_artin, hdegree,
    rayAbelianDegree_localRayAbsoluteArtin, hplaceDegree]

/-- The same reconstructed map preserves the actual ordinary unit quotients. -/
theorem localRayEquivOfArtinComparison_mem_units_iff (a : RayLocalFactor m₁ v₁) :
    localRayEquivOfArtinComparison m₁ v₁ m₂ v₂ e
        hclosure hdegree hplaceDegree hm₁ hm₂ a ∈ localRayFactorUnits m₂ v₂ ↔
      a ∈ localRayFactorUnits m₁ v₁ := by
  rw [← localRayFactorOrder_eq_one_iff m₂ v₂
      (localRayEquivOfArtinComparison m₁ v₁ m₂ v₂ e
        hclosure hdegree hplaceDegree hm₁ hm₂ a),
    ← localRayFactorOrder_eq_one_iff m₁ v₁ a,
    localRayEquivOfArtinComparison_order]

/-- Original Artin commutation makes the reconstructed local equivalence unique. -/
theorem localRayEquivOfArtinComparison_unique
    (ψ : RayLocalFactor m₁ v₁ ≃* RayLocalFactor m₂ v₂)
    (hψ : ∀ a, localRayAbsoluteArtin m₂ v₂ (ψ a) =
      e (localRayAbsoluteArtin m₁ v₁ a)) :
    ψ = localRayEquivOfArtinComparison m₁ v₁ m₂ v₂ e
      hclosure hdegree hplaceDegree hm₁ hm₂ := by
  apply MulEquiv.ext
  intro a
  apply localRayAbsoluteArtin_injective m₂ v₂ hm₂
  exact (hψ a).trans
    (localRayEquivOfArtinComparison_artin m₁ v₁ m₂ v₂ e
      hclosure hdegree hplaceDegree hm₁ hm₂ a).symm

/-- Recover the original local multiplicative group using only closed local
image and arithmetic degree preservation in the actual Artin quotients. -/
def localRayEquivOfClosure : RayLocalFactor m₁ v₁ ≃* RayLocalFactor m₂ v₂ :=
  localRayEquivOfArtinComparison m₁ v₁ m₂ v₂ e hclosure hdegree
    (fullConstant_placeDegree_eq_of_artinComparison m₁ v₁ m₂ v₂ e hclosure hdegree)
    hm₁ hm₂

/-- The equivalence recovered from closed images retains the original local symbols. -/
theorem localRayAbsoluteArtin_map (a : RayLocalFactor m₁ v₁) :
    localRayAbsoluteArtin m₂ v₂
        (localRayEquivOfClosure m₁ v₁ m₂ v₂ e hclosure hdegree hm₁ hm₂ a) =
      e (localRayAbsoluteArtin m₁ v₁ a) :=
  localRayEquivOfArtinComparison_artin m₁ v₁ m₂ v₂ e hclosure hdegree
    (fullConstant_placeDegree_eq_of_artinComparison m₁ v₁ m₂ v₂ e hclosure hdegree)
    hm₁ hm₂ a

/-- The equivalence recovered from closed images preserves normalized integer order. -/
theorem localRayFactorOrder_map (a : RayLocalFactor m₁ v₁) :
    localRayFactorOrder m₂ v₂
        (localRayEquivOfClosure m₁ v₁ m₂ v₂ e hclosure hdegree hm₁ hm₂ a) =
      localRayFactorOrder m₁ v₁ a :=
  localRayEquivOfArtinComparison_order m₁ v₁ m₂ v₂ e hclosure hdegree
    (fullConstant_placeDegree_eq_of_artinComparison m₁ v₁ m₂ v₂ e hclosure hdegree)
    hm₁ hm₂ a

/-- Ordinary local units are preserved without a separate unit comparison. -/
theorem localRayEquivOfClosure_mem_units_iff (a : RayLocalFactor m₁ v₁) :
    localRayEquivOfClosure m₁ v₁ m₂ v₂ e hclosure hdegree hm₁ hm₂ a ∈
        localRayFactorUnits m₂ v₂ ↔ a ∈ localRayFactorUnits m₁ v₁ :=
  localRayEquivOfArtinComparison_mem_units_iff m₁ v₁ m₂ v₂ e hclosure hdegree
    (fullConstant_placeDegree_eq_of_artinComparison m₁ v₁ m₂ v₂ e hclosure hdegree)
    hm₁ hm₂ a

/-- The local map recovered from closed images is the unique map commuting
with the given original Artin comparison. -/
theorem localRayEquivOfClosure_unique
    (ψ : RayLocalFactor m₁ v₁ ≃* RayLocalFactor m₂ v₂)
    (hψ : ∀ a, localRayAbsoluteArtin m₂ v₂ (ψ a) =
      e (localRayAbsoluteArtin m₁ v₁ a)) :
    ψ = localRayEquivOfClosure m₁ v₁ m₂ v₂ e hclosure hdegree hm₁ hm₂ :=
  localRayEquivOfArtinComparison_unique m₁ v₁ m₂ v₂ e hclosure hdegree
    (fullConstant_placeDegree_eq_of_artinComparison m₁ v₁ m₂ v₂ e hclosure hdegree)
    hm₁ hm₂ ψ hψ

end Comparison

end FunctionField.RayClass

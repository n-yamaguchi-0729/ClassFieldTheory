/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.FixedIdeles
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionUnramified
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayDegree
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.HigherUnitBaseChange
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayBaseChange

/-!
# Original local ray inclusions in finite extension towers

The literal completion inclusion preserves every principal-unit level.
It reflects reduced levels, all levels when unramified, and every
ramification-weighted divisor-pullback level. These local statements also
give injectivity of the corresponding restricted products before taking
a quotient by principal representatives.

The normalized order scales by the original ramification index. In the
actual finite constant stages the index is one, and the local transition
preserves the integer order exactly.
-/

@[expose] public section

universe u v w

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.RayClass

section FiniteExtension

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

/-- Both reduced local congruence levels are preserved and reflected by
the original completion map. -/
theorem localBaseChange_mem_reducedHigherUnit_iff
    (w : Place k L) (n : ℕ) (hn : n ≤ 1)
    (x : (w.restrict K).adicCompletionˣ) :
    IdeleGroup.localBaseChange (K := K) w x ∈ localHigherUnitGroup w n ↔
      x ∈ localHigherUnitGroup (w.restrict K) n := by
  rcases Nat.eq_zero_or_pos n with hzero | hpos
  · rw [hzero]
    simp only [localHigherUnitGroup_zero]
    exact IdeleGroup.localBaseChange_mem_localUnits_iff w x
  · have hone : n = 1 := Nat.le_antisymm hn hpos
    rw [hone]
    exact localBaseChange_mem_firstHigherUnit_iff w x

/-- The original completion inclusion on local ray factors at every multiplicity. -/
def localRayBaseChange (m : Modulus k K) (w : Place k L) :
    RayLocalFactor m (w.restrict K) →*
      RayLocalFactor (reindexAlongPlaces L m) w :=
  QuotientGroup.map (localHigherUnitGroup (w.restrict K) (m (w.restrict K)))
    (localHigherUnitGroup w (reindexAlongPlaces L m w))
    (IdeleGroup.localBaseChange (K := K) w)
    (fun x hx =>
      localBaseChange_mem_higherUnit w (m (w.restrict K)) x hx)

/-- Representatives are sent through the original completion inclusion. -/
theorem localRayBaseChange_mk (m : Modulus k K)
    (w : Place k L) (x : (w.restrict K).adicCompletionˣ) :
    localRayBaseChange (L := L) m w
        (QuotientGroup.mk' (localHigherUnitGroup (w.restrict K) (m (w.restrict K))) x) =
      QuotientGroup.mk' (localHigherUnitGroup w (reindexAlongPlaces L m w))
        (IdeleGroup.localBaseChange (K := K) w x) := rfl

/-- No reduced local ray class is lost under actual finite extension. -/
theorem localRayBaseChange_injective (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (w : Place k L) : Function.Injective (localRayBaseChange (L := L) m w) := by
  apply (injective_iff_map_eq_one (localRayBaseChange (L := L) m w)).mpr
  intro a ha
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (localHigherUnitGroup (w.restrict K) (m (w.restrict K))) a
  apply (QuotientGroup.eq_one_iff x).mpr
  apply (localBaseChange_mem_reducedHigherUnit_iff
    w (m (w.restrict K)) (hm _) x).mp
  exact (QuotientGroup.eq_one_iff (IdeleGroup.localBaseChange (K := K) w x)).mp ha

/-- The actual local order changes by its original ramification index. -/
theorem localRayFactorOrder_baseChange (m : Modulus k K)
    (w : Place k L) (a : RayLocalFactor m (w.restrict K)) :
    (localRayFactorOrder (reindexAlongPlaces L m) w
        (localRayBaseChange (L := L) m w a)).toAdd =
      (w.ramificationIndex K : ℤ) * (localRayFactorOrder m (w.restrict K) a).toAdd := by
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (localHigherUnitGroup (w.restrict K) (m (w.restrict K))) a
  rw [localRayBaseChange_mk, localRayFactorOrder_mk, localRayFactorOrder_mk]
  exact IdeleGroup.localOrder_completionMap w x

/-- The local unit classes are preserved and reflected at every finite stage. -/
theorem localRayBaseChange_mem_units_iff
    (m : Modulus k K)
    (w : Place k L) (a : RayLocalFactor m (w.restrict K)) :
    localRayBaseChange (L := L) m w a ∈
        localRayFactorUnits (reindexAlongPlaces L m) w ↔
      a ∈ localRayFactorUnits m (w.restrict K) := by
  rw [← localRayFactorOrder_eq_one_iff (reindexAlongPlaces L m) w
      (localRayBaseChange (L := L) m w a),
    ← localRayFactorOrder_eq_one_iff m (w.restrict K) a]
  constructor
  · intro h
    apply Multiplicative.ext
    have hzero : (w.ramificationIndex K : ℤ) *
        (localRayFactorOrder m (w.restrict K) a).toAdd = 0 := by
      rw [← localRayFactorOrder_baseChange m w a, h]
      rfl
    exact (mul_eq_zero.mp hzero).resolve_left
      (Int.natCast_ne_zero.mpr (w.ramificationIndex_pos (F := K)).ne')
  · intro h
    apply Multiplicative.ext
    rw [localRayFactorOrder_baseChange, h]
    exact mul_zero _

/-- Every restricted-ray coordinate is the corresponding original local transition. -/
theorem restrictedRayBaseChange_apply (m : Modulus k K)
    (a : RayRestrictedProduct m) (w : Place k L) :
    restrictedRayBaseChange (L := L) m a w =
      localRayBaseChange (L := L) m w (a (w.restrict K)) := by
  obtain ⟨b, rfl⟩ := ideleToRayRestrictedProduct_surjective m a
  rw [restrictedRayBaseChange_idele_apply]
  rfl

/-- The original reduced restricted-ray transition is injective on all families. -/
theorem restrictedRayBaseChange_injective (m : Modulus k K) (hm : ∀ v, m v ≤ 1) :
    Function.Injective (restrictedRayBaseChange (L := L) m) := by
  intro a b hab
  apply RestrictedProduct.ext
  intro v
  obtain ⟨w, rfl⟩ := Place.exists_restrict_eq (M := L) v
  apply localRayBaseChange_injective m hm w
  have h := congrArg (fun c : RayRestrictedProduct (reindexAlongPlaces L m) => c w) hab
  exact (restrictedRayBaseChange_apply m a w).symm.trans
    (h.trans (restrictedRayBaseChange_apply m b w))

/-- The completion inclusion is injective on every local ray factor when
its ramification index is one. -/
theorem localRayBaseChange_injective_of_unramified (m : Modulus k K)
    (w : Place k L) (he : w.ramificationIndex K = 1) :
    Function.Injective (localRayBaseChange (L := L) m w) := by
  apply (injective_iff_map_eq_one (localRayBaseChange (L := L) m w)).mpr
  intro a ha
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (localHigherUnitGroup (w.restrict K) (m (w.restrict K))) a
  apply (QuotientGroup.eq_one_iff x).mpr
  apply (localBaseChange_mem_higherUnit_iff_of_unramified w he (m (w.restrict K)) x).mp
  exact (QuotientGroup.eq_one_iff (IdeleGroup.localBaseChange (K := K) w x)).mp ha

/-- The full restricted-ray transition is injective at an everywhere
unramified extension, with arbitrary boundary multiplicities. -/
theorem restrictedRayBaseChange_injective_of_unramified (m : Modulus k K)
    (he : ∀ w : Place k L, w.ramificationIndex K = 1) :
    Function.Injective (restrictedRayBaseChange (L := L) m) := by
  intro a b hab
  apply RestrictedProduct.ext
  intro v
  obtain ⟨w, rfl⟩ := Place.exists_restrict_eq (M := L) v
  apply localRayBaseChange_injective_of_unramified m w (he w)
  have h := congrArg (fun c : RayRestrictedProduct (reindexAlongPlaces L m) => c w) hab
  exact (restrictedRayBaseChange_apply m a w).symm.trans
    (h.trans (restrictedRayBaseChange_apply m b w))

/-- Divisor pullback uses the ramification-weighted target depth on the same
actual completion map. -/
def localRayPullbackDivisor (m : Modulus k K) (w : Place k L) :
    RayLocalFactor m (w.restrict K) →* RayLocalFactor (pullbackDivisor L m) w :=
  QuotientGroup.map (localHigherUnitGroup (w.restrict K) (m (w.restrict K)))
    (localHigherUnitGroup w (pullbackDivisor L m w))
    (IdeleGroup.localBaseChange (K := K) w)
    (fun x hx => (localBaseChange_mem_mulHigherUnit_iff w (m (w.restrict K)) x).mpr hx)

/-- The divisor-pullback map sends each representative through the same completion inclusion. -/
theorem localRayPullbackDivisor_mk (m : Modulus k K) (w : Place k L)
    (x : (w.restrict K).adicCompletionˣ) :
    localRayPullbackDivisor (L := L) m w
        (QuotientGroup.mk' (localHigherUnitGroup (w.restrict K) (m (w.restrict K))) x) =
      QuotientGroup.mk' (localHigherUnitGroup w (pullbackDivisor L m w))
        (IdeleGroup.localBaseChange (K := K) w x) := rfl

/-- Local ray classes inject into the ramification-weighted divisor-pullback
quotient, without any reducedness assumption. -/
theorem localRayPullbackDivisor_injective (m : Modulus k K) (w : Place k L) :
    Function.Injective (localRayPullbackDivisor (L := L) m w) := by
  apply (injective_iff_map_eq_one (localRayPullbackDivisor (L := L) m w)).mpr
  intro a ha
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (localHigherUnitGroup (w.restrict K) (m (w.restrict K))) a
  apply (QuotientGroup.eq_one_iff x).mpr
  apply (localBaseChange_mem_mulHigherUnit_iff w (m (w.restrict K)) x).mp
  exact (QuotientGroup.eq_one_iff (IdeleGroup.localBaseChange (K := K) w x)).mp ha

/-- Divisor-pullback local orders scale by the same ramification index. -/
theorem localRayFactorOrder_pullbackDivisor (m : Modulus k K)
    (w : Place k L) (a : RayLocalFactor m (w.restrict K)) :
    (localRayFactorOrder (pullbackDivisor L m) w
        (localRayPullbackDivisor (L := L) m w a)).toAdd =
      (w.ramificationIndex K : ℤ) * (localRayFactorOrder m (w.restrict K) a).toAdd := by
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (localHigherUnitGroup (w.restrict K) (m (w.restrict K))) a
  rw [localRayPullbackDivisor_mk, localRayFactorOrder_mk, localRayFactorOrder_mk]
  exact IdeleGroup.localOrder_completionMap w x

end FiniteExtension

section ConstantExtension

variable {k : Type u} {K : Type v} [Field k] [Finite k] [Field K] [Algebra k K]
    [HasPrincipalDivisors k K] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    (Ω : Type w) [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [IsSepClosed Ω]

omit [HasPrincipalDivisors k K] in
/-- The actual finite constant stages preserve normalized local ray order
before restricting to the original principal kernel. -/
theorem localRayFactorOrder_fullConstant_baseChange
    (n : ℕ) [NeZero n] (m : Modulus k K) :
    let E := fullConstantDegreeStage k K Ω n
    ∀ (w : Place k E) (a : RayLocalFactor m (w.restrict K)),
      localRayFactorOrder (reindexAlongPlaces E m) w
          (localRayBaseChange (L := E) m w a) =
        localRayFactorOrder m (w.restrict K) a := by
  intro E w a
  apply Multiplicative.ext
  rw [localRayFactorOrder_baseChange,
    ramificationIndex_fullConstantDegreeStage k K Ω n w, Nat.cast_one, one_mul]

omit [HasPrincipalDivisors k K] in
/-- Finite constant extension preserves all restricted-ray multiplicities
and is injective before quotienting by principal representatives. -/
theorem restrictedRayBaseChange_fullConstant_injective
    (n : ℕ) [NeZero n] (m : Modulus k K) :
    Function.Injective
      (restrictedRayBaseChange (L := fullConstantDegreeStage k K Ω n) m) :=
  restrictedRayBaseChange_injective_of_unramified m
    (ramificationIndex_fullConstantDegreeStage k K Ω n)

end ConstantExtension

end FunctionField.RayClass

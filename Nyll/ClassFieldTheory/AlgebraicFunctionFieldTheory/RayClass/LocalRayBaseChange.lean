/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.FixedIdeles
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayDegree
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayBaseChange

/-!
# Original local ray inclusions in finite extension towers

The literal completion inclusion preserves and reflects the ordinary units
and the full first principal units. It therefore gives an injective map on
each reduced local ray factor. Every coordinate of the original restricted
ray base change is this local map, so the whole restricted ray transition
is injective before passage to the principal kernel.

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

/-- The original completion inclusion on the actual reduced local ray factors. -/
def localRayBaseChange (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (w : Place k L) :
    RayLocalFactor m (w.restrict K) →*
      RayLocalFactor (rayModulusBaseChange L m) w :=
  QuotientGroup.map (localHigherUnitGroup (w.restrict K) (m (w.restrict K)))
    (localHigherUnitGroup w (rayModulusBaseChange L m w))
    (IdeleGroup.localBaseChange (K := K) w)
    (fun x hx =>
      (localBaseChange_mem_reducedHigherUnit_iff w (m (w.restrict K)) (hm _) x).mpr hx)

/-- Representatives are sent through the original completion inclusion. -/
theorem localRayBaseChange_mk (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (w : Place k L) (x : (w.restrict K).adicCompletionˣ) :
    localRayBaseChange (L := L) m hm w
        (QuotientGroup.mk' (localHigherUnitGroup (w.restrict K) (m (w.restrict K))) x) =
      QuotientGroup.mk' (localHigherUnitGroup w (rayModulusBaseChange L m w))
        (IdeleGroup.localBaseChange (K := K) w x) := rfl

/-- No reduced local ray class is lost under actual finite extension. -/
theorem localRayBaseChange_injective (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (w : Place k L) : Function.Injective (localRayBaseChange (L := L) m hm w) := by
  apply (injective_iff_map_eq_one (localRayBaseChange (L := L) m hm w)).mpr
  intro a ha
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (localHigherUnitGroup (w.restrict K) (m (w.restrict K))) a
  apply (QuotientGroup.eq_one_iff x).mpr
  apply (localBaseChange_mem_reducedHigherUnit_iff
    w (m (w.restrict K)) (hm _) x).mp
  exact (QuotientGroup.eq_one_iff (IdeleGroup.localBaseChange (K := K) w x)).mp ha

/-- The actual local order changes by its original ramification index. -/
theorem localRayFactorOrder_baseChange (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (w : Place k L) (a : RayLocalFactor m (w.restrict K)) :
    (localRayFactorOrder (rayModulusBaseChange L m) w
        (localRayBaseChange (L := L) m hm w a)).toAdd =
      (w.ramificationIndex K : ℤ) * (localRayFactorOrder m (w.restrict K) a).toAdd := by
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (localHigherUnitGroup (w.restrict K) (m (w.restrict K))) a
  rw [localRayBaseChange_mk, localRayFactorOrder_mk, localRayFactorOrder_mk]
  exact IdeleGroup.localOrder_completionMap w x

/-- The local unit classes are preserved and reflected at every finite stage. -/
theorem localRayBaseChange_mem_units_iff
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (w : Place k L) (a : RayLocalFactor m (w.restrict K)) :
    localRayBaseChange (L := L) m hm w a ∈
        localRayFactorUnits (rayModulusBaseChange L m) w ↔
      a ∈ localRayFactorUnits m (w.restrict K) := by
  rw [← localRayFactorOrder_eq_one_iff (rayModulusBaseChange L m) w
      (localRayBaseChange (L := L) m hm w a),
    ← localRayFactorOrder_eq_one_iff m (w.restrict K) a]
  constructor
  · intro h
    apply Multiplicative.ext
    have hzero : (w.ramificationIndex K : ℤ) *
        (localRayFactorOrder m (w.restrict K) a).toAdd = 0 := by
      rw [← localRayFactorOrder_baseChange m hm w a, h]
      rfl
    exact (mul_eq_zero.mp hzero).resolve_left
      (Int.natCast_ne_zero.mpr (w.ramificationIndex_pos (F := K)).ne')
  · intro h
    apply Multiplicative.ext
    rw [localRayFactorOrder_baseChange, h]
    exact mul_zero _

/-- Every restricted-ray coordinate is the corresponding original local transition. -/
theorem restrictedRayBaseChange_apply (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (a : RayRestrictedProduct m) (w : Place k L) :
    restrictedRayBaseChange (L := L) m hm a w =
      localRayBaseChange (L := L) m hm w (a (w.restrict K)) := by
  obtain ⟨b, rfl⟩ := ideleToRayRestrictedProduct_surjective m a
  rw [restrictedRayBaseChange_idele_apply]
  rfl

/-- The original reduced restricted-ray transition is injective on all families. -/
theorem restrictedRayBaseChange_injective (m : Modulus k K) (hm : ∀ v, m v ≤ 1) :
    Function.Injective (restrictedRayBaseChange (L := L) m hm) := by
  intro a b hab
  apply RestrictedProduct.ext
  intro v
  obtain ⟨w, rfl⟩ := Place.exists_restrict_eq (M := L) v
  apply localRayBaseChange_injective m hm w
  have h := congrArg (fun c : RayRestrictedProduct (rayModulusBaseChange L m) => c w) hab
  exact (restrictedRayBaseChange_apply m hm a w).symm.trans
    (h.trans (restrictedRayBaseChange_apply m hm b w))

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
    (n : ℕ) [NeZero n] (m : Modulus k K) (hm : ∀ v, m v ≤ 1) :
    let E := fullConstantDegreeStage k K Ω n
    ∀ (w : Place k E) (a : RayLocalFactor m (w.restrict K)),
      localRayFactorOrder (rayModulusBaseChange E m) w
          (localRayBaseChange (L := E) m hm w a) =
        localRayFactorOrder m (w.restrict K) a := by
  intro E w a
  apply Multiplicative.ext
  rw [localRayFactorOrder_baseChange,
    ramificationIndex_fullConstantDegreeStage k K Ω n w, Nat.cast_one, one_mul]

end ConstantExtension

end FunctionField.RayClass

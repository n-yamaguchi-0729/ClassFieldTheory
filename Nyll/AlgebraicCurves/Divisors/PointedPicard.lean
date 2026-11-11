/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardDegree
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! # Removing degree at an actual degree-one place -/

@[expose] public section

noncomputable section

namespace AlgebraicCurve

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace Divisor

/-- Subtract the degree at the specified degree-one place. -/
def degreeZeroProjection (ε : Place k K) (hε : ε.deg = 1) :
    Divisor k K →+ degZero (K := k) (F := K) where
  toFun D := ⟨D - Finsupp.single ε (degree D), by
    change degree (D - Finsupp.single ε (degree D)) = 0
    rw [map_sub, degree_single, hε, Nat.cast_one, mul_one, sub_self]⟩
  map_zero' := by
    apply Subtype.ext
    change 0 - Finsupp.single ε (degree 0) = 0
    rw [map_zero, Finsupp.single_zero, sub_self]
  map_add' D E := by
    apply Subtype.ext
    change D + E - Finsupp.single ε (degree (D + E)) =
      (D - Finsupp.single ε (degree D)) + (E - Finsupp.single ε (degree E))
    rw [map_add, Finsupp.single_add]
    abel

theorem degreeZeroProjection_of_degreeZero (ε : Place k K) (hε : ε.deg = 1)
    (D : degZero (K := k) (F := K)) :
    degreeZeroProjection ε hε (D : Divisor k K) = D := by
  apply Subtype.ext
  change (D : Divisor k K) - Finsupp.single ε (degree (D : Divisor k K)) = D
  rw [D.property, Finsupp.single_zero, sub_zero]

end Divisor

namespace Pic0

variable [HasPrincipalDivisors k K]

/-- The actual retraction from divisor classes to degree-zero divisor
classes determined by the chosen degree-one place. -/
def pointedClass (ε : Place k K) (hε : ε.deg = 1) : Pic k K →+ Pic0 k K :=
  QuotientAddGroup.lift Divisor.principal
    ((QuotientAddGroup.mk'
      ((Divisor.principal (K := k) (F := K)).addSubgroupOf Divisor.degZero)).comp
        (Divisor.degreeZeroProjection ε hε)) (by
      intro D hD
      apply (QuotientAddGroup.eq_zero_iff (Divisor.degreeZeroProjection ε hε D)).mpr
      change D - Finsupp.single ε (Divisor.degree D) ∈ Divisor.principal
      rw [Divisor.degree_eq_zero_of_isPrincipal hD, Finsupp.single_zero, sub_zero]
      exact hD)

theorem pointedClass_mk (ε : Place k K) (hε : ε.deg = 1) (D : Divisor k K) :
    pointedClass ε hε (H1Gm.mk D) = mk (Divisor.degreeZeroProjection ε hε D) := rfl

theorem pointedClass_ofPic0 (ε : Place k K) (hε : ε.deg = 1) (c : Pic0 k K) :
    pointedClass ε hε (H1Gm.ofPic0 k K c) = c := by
  obtain ⟨D, rfl⟩ := mk_surjective c
  rw [H1Gm.ofPic0_mk, pointedClass_mk, Divisor.degreeZeroProjection_of_degreeZero]

theorem pointedClass_surjective (ε : Place k K) (hε : ε.deg = 1) :
    Function.Surjective (pointedClass ε hε) :=
  fun c => ⟨H1Gm.ofPic0 k K c, pointedClass_ofPic0 ε hε c⟩

/-- The retraction has the expected value in the original full Picard group. -/
theorem ofPic0_pointedClass (ε : Place k K) (hε : ε.deg = 1) (c : Pic k K) :
    H1Gm.ofPic0 k K (pointedClass ε hε c) =
      c - H1Gm.mk (Finsupp.single ε (H1Gm.degree k K c)) := by
  obtain ⟨D, rfl⟩ := H1Gm.mk_surjective c
  rw [pointedClass_mk, H1Gm.ofPic0_mk, H1Gm.degree_mk]
  exact map_sub (QuotientAddGroup.mk' Divisor.principal) D
    (Finsupp.single ε (Divisor.degree D))

/-- The exact kernel consists of the classes supported at the specified place. -/
theorem pointedClass_eq_zero_iff (ε : Place k K) (hε : ε.deg = 1) (c : Pic k K) :
    pointedClass ε hε c = 0 ↔
      c = H1Gm.mk (Finsupp.single ε (H1Gm.degree k K c)) := by
  constructor
  · intro hc
    have h := congrArg (H1Gm.ofPic0 k K) hc
    rw [ofPic0_pointedClass, map_zero, sub_eq_zero] at h
    exact h
  · intro hc
    apply H1Gm.ofPic0_injective k K
    rw [ofPic0_pointedClass, map_zero, sub_eq_zero]
    exact hc

/-- The class of the original closed-point divisor after removing its degree. -/
def placeDifference (ε : Place k K) (hε : ε.deg = 1) (v : Place k K) : Pic0 k K :=
  pointedClass ε hε (H1Gm.mk (Finsupp.single v 1))

theorem ofPic0_placeDifference (ε : Place k K) (hε : ε.deg = 1) (v : Place k K) :
    H1Gm.ofPic0 k K (placeDifference ε hε v) =
      H1Gm.mk (Finsupp.single v 1) - H1Gm.mk (Finsupp.single ε (v.deg : ℤ)) := by
  rw [placeDifference, ofPic0_pointedClass, H1Gm.degree_mk, Divisor.degree_single, one_mul]

/-- All degree-zero classes are finite integral sums of the original
closed-point classes `[v - deg(v) ε]`. -/
theorem exists_sum_placeDifference (ε : Place k K) (hε : ε.deg = 1) (c : Pic0 k K) :
    ∃ D : Divisor k K, c = D.sum (fun v n => n • placeDifference ε hε v) := by
  let f : Divisor k K →+ Pic0 k K :=
    (pointedClass ε hε).comp (QuotientAddGroup.mk' Divisor.principal)
  have hsingle (v : Place k K) (n : ℤ) :
      f (Finsupp.single v n) = n • placeDifference ε hε v := by
    rw [← Finsupp.smul_single_one v n, map_zsmul]
    rfl
  obtain ⟨D, rfl⟩ := mk_surjective c
  refine ⟨D, ?_⟩
  have h := map_finsuppSum f (D : Divisor k K) Finsupp.single
  rw [Finsupp.sum_single] at h
  simp only [hsingle] at h
  change pointedClass ε hε (H1Gm.mk (D : Divisor k K)) = _ at h
  rw [pointedClass_mk, Divisor.degreeZeroProjection_of_degreeZero] at h
  exact h

end Pic0

end AlgebraicCurve

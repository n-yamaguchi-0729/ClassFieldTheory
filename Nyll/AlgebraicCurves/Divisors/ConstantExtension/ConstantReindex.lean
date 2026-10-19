/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Tactic.Ring
import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantExtension
import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardDegree

/-!
# Divisor and Picard reindexing after changing the constant field

The actual equivalence of places preserves principal divisors and scales
arithmetic degree by the degree of the constant extension. The existing
FunctionField declaration names are retained for downstream compatibility.
-/

noncomputable section

namespace FunctionField

open AlgebraicCurve

section ConstantExtension

variable (k C K : Type*) [Field k] [Field C] [Field K]
    [Algebra k C] [Algebra k K] [Algebra C K] [IsScalarTower k C K]
    [Algebra.IsIntegral k C]

/-- Reindex the existing divisors along the actual equivalence of places. -/
def divisorConstantEquiv : Divisor k K ≃+ Divisor C K :=
  Finsupp.domCongr (Place.constantFieldEquiv k C)

@[simp]
theorem divisorConstantEquiv_apply (D : Divisor k K) (w : Place C K) :
    divisorConstantEquiv k C K D w = D (w.forgetConstants (K := k)) :=
  Finsupp.equivMapDomain_apply (Place.constantFieldEquiv k C) D w

/-- Reindexing sends a single place to its extension of constants. -/
theorem divisorConstantEquiv_single (v : Place k K) (n : ℤ) :
    divisorConstantEquiv k C K (Finsupp.single v n) =
      Finsupp.single (v.extendConstants C) n :=
  Finsupp.equivMapDomain_single (Place.constantFieldEquiv k C) v n

/-- The reindexing preserves each principal divisor, with the same defining function. -/
theorem isPrincipal_divisorConstantEquiv_iff (D : Divisor k K) :
    Divisor.IsPrincipal (divisorConstantEquiv k C K D) ↔ Divisor.IsPrincipal D := by
  constructor
  · rintro ⟨f, hf, hD⟩
    refine ⟨f, hf, fun v => ?_⟩
    have h := hD (v.extendConstants C)
    rw [divisorConstantEquiv_apply] at h
    exact h
  · rintro ⟨f, hf, hD⟩
    refine ⟨f, hf, fun w => ?_⟩
    rw [divisorConstantEquiv_apply]
    exact hD (w.forgetConstants (K := k))

/-- Divisor degrees scale by the degree of the finite extension of constants. -/
theorem degree_divisorConstantEquiv (D : Divisor k K) :
    Divisor.degree D = (Module.finrank k C : ℤ) *
      Divisor.degree (divisorConstantEquiv k C K D) := by
  let e := divisorConstantEquiv k C K
  let δ : Divisor k K →+ ℤ := (AddMonoidHom.mulLeft (Module.finrank k C : ℤ)).comp
    (Divisor.degree.comp e.toAddMonoidHom)
  have h : (Divisor.degree : Divisor k K →+ ℤ) = δ := by
    apply Finsupp.addHom_ext
    intro v n
    change Divisor.degree (Finsupp.single v n) = (Module.finrank k C : ℤ) *
      Divisor.degree (Finsupp.equivMapDomain (Place.constantFieldEquiv k C)
        (Finsupp.single v n))
    rw [Finsupp.equivMapDomain_single, Divisor.degree_single, Divisor.degree_single]
    have hd : (v.deg : ℤ) = (Module.finrank k C : ℤ) *
        ((v.extendConstants C).deg : ℤ) := by
      exact_mod_cast Place.deg_forgetConstants (K := k) (v.extendConstants C)
    rw [hd]
    change n * ((Module.finrank k C : ℤ) * ((v.extendConstants C).deg : ℤ)) =
      (Module.finrank k C : ℤ) * (n * ((v.extendConstants C).deg : ℤ))
    ring
  exact DFunLike.congr_fun h D

/-- Principal divisors descend when algebraically extended constants are forgotten. -/
theorem hasPrincipalDivisors_of_extendedConstants [HasPrincipalDivisors C K] :
    HasPrincipalDivisors k K := by
  constructor
  intro f hf
  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := C) f hf
  let e := divisorConstantEquiv k C K
  refine ⟨e.symm D, ?_, ?_⟩
  · intro v
    have h := hD (v.extendConstants C)
    have he : e (e.symm D) = D := e.apply_symm_apply D
    rw [← he, divisorConstantEquiv_apply] at h
    exact h
  · rw [degree_divisorConstantEquiv k C K, AddEquiv.apply_symm_apply, hdeg, mul_zero]

/-- Principal divisors remain of degree zero after a finite change of constants. -/
theorem hasPrincipalDivisors_extendedConstants [FiniteDimensional k C]
    [HasPrincipalDivisors k K] : HasPrincipalDivisors C K := by
  constructor
  intro f hf
  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := k) f hf
  refine ⟨divisorConstantEquiv k C K D, fun w => ?_, ?_⟩
  · rw [divisorConstantEquiv_apply]
    exact hD (w.forgetConstants (K := k))
  · have hd := degree_divisorConstantEquiv k C K D
    rw [hdeg] at hd
    exact (mul_eq_zero.mp hd.symm).resolve_left
      (Int.natCast_ne_zero.mpr (Module.finrank_pos (R := k) (M := C)).ne')

/-- Changing algebraic constants inside the same field preserves the full Picard group. -/
def picConstantEquiv : Pic k K ≃+ Pic C K := by
  let e := divisorConstantEquiv k C K
  refine QuotientAddGroup.congr _ _ e ?_
  ext D
  constructor
  · rintro ⟨E, hE, rfl⟩
    exact (isPrincipal_divisorConstantEquiv_iff k C K E).mpr hE
  · intro hD
    refine ⟨e.symm D, ?_, e.apply_symm_apply D⟩
    apply (isPrincipal_divisorConstantEquiv_iff k C K (e.symm D)).mp
    rw [e.apply_symm_apply]
    exact hD

/-- The full Picard reindexing is computed on actual divisor representatives. -/
theorem picConstantEquiv_mk (D : Divisor k K) :
    picConstantEquiv k C K (H1Gm.mk D) = H1Gm.mk (divisorConstantEquiv k C K D) := rfl

/-- The degree scales by the actual extension degree of constants. -/
theorem degree_picConstantEquiv [HasPrincipalDivisors k K] [HasPrincipalDivisors C K]
    (x : Pic k K) :
    H1Gm.degree k K x = (Module.finrank k C : ℤ) *
      H1Gm.degree C K (picConstantEquiv k C K x) := by
  obtain ⟨D, rfl⟩ := H1Gm.mk_surjective x
  exact degree_divisorConstantEquiv k C K D

variable [Module.Finite k C]

/-- Reindexing along constant extension identifies the actual degree-zero divisor subgroups. -/
def degreeZeroConstantEquiv : Divisor.degZero (K := k) (F := K) ≃+
    Divisor.degZero (K := C) (F := K) where
  toFun D := ⟨divisorConstantEquiv k C K D, by
    apply Divisor.mem_degZero.mpr
    have hd : (Module.finrank k C : ℤ) ≠ 0 := by
      exact_mod_cast (Module.finrank_pos (R := k) (M := C)).ne'
    have hprod : (Module.finrank k C : ℤ) *
        Divisor.degree (divisorConstantEquiv k C K D) = 0 :=
      (degree_divisorConstantEquiv k C K D).symm.trans (Divisor.mem_degZero.mp D.2)
    exact (mul_eq_zero.mp hprod).resolve_left hd⟩
  invFun D := ⟨(divisorConstantEquiv k C K).symm D, by
    apply Divisor.mem_degZero.mpr
    rw [degree_divisorConstantEquiv k C K, AddEquiv.apply_symm_apply,
      Divisor.mem_degZero.mp D.2, mul_zero]⟩
  left_inv D := Subtype.ext ((divisorConstantEquiv k C K).symm_apply_apply D)
  right_inv D := Subtype.ext ((divisorConstantEquiv k C K).apply_symm_apply D)
  map_add' D E := Subtype.ext ((divisorConstantEquiv k C K).map_add D E)

/-- Constant extension within the same function field preserves the degree-zero Picard group. -/
def pic0ConstantEquiv : Pic0 k K ≃+ Pic0 C K := by
  let e := degreeZeroConstantEquiv k C K
  refine QuotientAddGroup.congr _ _ e ?_
  ext D
  constructor
  · rintro ⟨E, hE, rfl⟩
    change Divisor.IsPrincipal (divisorConstantEquiv k C K (E : Divisor k K))
    exact (isPrincipal_divisorConstantEquiv_iff k C K E).mpr hE
  · intro hD
    refine ⟨e.symm D, ?_, e.apply_symm_apply D⟩
    change Divisor.IsPrincipal ((divisorConstantEquiv k C K).symm (D : Divisor C K))
    apply (isPrincipal_divisorConstantEquiv_iff k C K
      ((divisorConstantEquiv k C K).symm D)).mp
    rw [AddEquiv.apply_symm_apply]
    exact hD

end ConstantExtension

end FunctionField

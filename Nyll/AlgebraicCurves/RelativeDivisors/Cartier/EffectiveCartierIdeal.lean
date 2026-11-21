/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.Cartier
public import Nyll.SchemeTheory.Divisors.Basic
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Original invertible ideals are effective Cartier ideals

The existing invertibility condition supplies actual principal affine basic
opens and actual non-zero-divisor generators. Those same equations satisfy
the effective Cartier condition used in scheme theory.
-/

@[expose] public section

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Reuse the literal local equations in the original invertibility
condition as the equations of an effective Cartier divisor. -/
theorem IsInvertible.isEffectiveCartier
    {X : Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsInvertible) :
    I.IsEffectiveCartier := by
  intro x
  obtain ⟨U, f, hx, g, hg, hIg⟩ := hI x
  refine ⟨X.affineBasicOpen f, hx, g, ?_, hIg⟩
  constructor
  · intro a b hab
    change g * a = g * b at hab
    apply sub_eq_zero.mp
    apply (mem_nonZeroDivisors_iff.mp hg).1
    rw [mul_sub, hab, sub_self]
  · intro a b hab
    change a * g = b * g at hab
    apply sub_eq_zero.mp
    apply (mem_nonZeroDivisors_iff.mp hg).2
    rw [sub_mul, hab, sub_self]

end AlgebraicGeometry.Scheme.IdealSheafData

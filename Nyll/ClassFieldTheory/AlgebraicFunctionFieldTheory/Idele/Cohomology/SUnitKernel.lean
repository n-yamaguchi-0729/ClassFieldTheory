/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Finiteness.Finsupp
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.SUnits
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FullConstants

/-!
# The finite kernel of the S-unit divisor map

A function in the kernel of the actual S-unit divisor map has no poles at any
place. Over the actual full field of constants such a function belongs to
`LSpace 0`, which consists precisely of constants. The full constant field is
finite, so the kernel is finite. Together with the finite divisor cokernel this
gives the finite errors needed to compare S-units with their divisor lattice.
-/

noncomputable section

namespace FunctionField.SUnits

open AlgebraicCurve

variable {k K : Type*} [Field k] [Field K] [Algebra k K]
    [HasPrincipalDivisors k K]

/-- An S-unit has zero divisor exactly when all of its actual place orders vanish. -/
theorem divisor_eq_zero_iff (S : Finset (Place k K)) (x : Additive (units k K S)) :
    divisor S x = 0 ↔ ∀ v : Place k K, v.ord ((x.toMul : Kˣ) : K) = 0 := by
  constructor
  · intro hx v
    have h := congrArg (fun D : divisorLattice k K S => (D : Divisor k K) v) hx
    change (divisor S x : Divisor k K) v = 0 at h
    rw [divisor_apply] at h
    exact h
  · intro hx
    apply Subtype.ext
    apply Finsupp.ext
    intro v
    change (divisor S x : Divisor k K) v = 0
    rw [divisor_apply, hx v]

variable (k K) [Finite k] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K]

omit [HasPrincipalDivisors k K] in
/-- Functions without poles form a finite set over the actual full constant field. -/
theorem finite_lSpace_zero_fullConstants :
    Finite (LSpace (0 : Divisor (algebraicClosure k K) K)) := by
  have : Algebra.EssFiniteType k K := FunctionField.essFiniteType k K
  have : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  let f : algebraicClosure k K → LSpace (0 : Divisor (algebraicClosure k K) K) :=
    fun c => ⟨algebraMap (algebraicClosure k K) K c, algebraMap_mem_lSpace_zero c⟩
  apply Finite.of_surjective f
  intro x
  have hx : (x : K) ∈ LinearMap.range (Algebra.linearMap (algebraicClosure k K) K) := by
    rw [← FunctionField.constantsAreBase_fullConstants k K]
    exact x.2
  obtain ⟨c, hc⟩ := hx
  exact ⟨c, Subtype.ext hc⟩

/-- The kernel of the actual S-unit divisor map is finite over a finite field. -/
theorem finite_ker_divisor (S : Finset (Place k K)) : Finite (divisor S).ker := by
  have : Finite (LSpace (0 : Divisor (algebraicClosure k K) K)) :=
    finite_lSpace_zero_fullConstants k K
  let f : (divisor S).ker → LSpace (0 : Divisor (algebraicClosure k K) K) :=
    fun x => ⟨((x.val.toMul : Kˣ) : K), by
      apply mem_lSpace_iff_ord.mpr
      right
      intro v
      have hord := (divisor_eq_zero_iff S x.val).mp x.2
        (v.forgetConstants (K := k))
      change v.ord ((x.val.toMul : Kˣ) : K) = 0 at hord
      change 0 ≤ v.ord ((x.val.toMul : Kˣ) : K)
      exact hord.ge⟩
  apply Finite.of_injective f
  intro x y h
  apply Subtype.ext
  change x.val.toMul = y.val.toMul
  apply Subtype.ext
  apply Units.ext
  exact congrArg Subtype.val h

/-- Actual S-units are finitely generated: their divisor image is contained in
an integral lattice of finite rank and their divisor kernel is finite. -/
theorem finite_units (S : Finset (Place k K)) :
    Module.Finite ℤ (Additive (units k K S)) := by
  let f : Additive (units k K S) →ₗ[ℤ] divisorLattice k K S :=
    (divisor S).toIntLinearMap
  have hL : Module.Finite ℤ (divisorLattice k K S) := finite_divisorLattice S
  have hker : Finite f.ker := finite_ker_divisor k K S
  have hkerFG : Module.Finite ℤ f.ker := inferInstance
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker f ?_ ?_⟩
  · exact IsNoetherian.noetherian _
  · rw [top_inf_eq]
    exact Submodule.FG.of_finite

end FunctionField.SUnits

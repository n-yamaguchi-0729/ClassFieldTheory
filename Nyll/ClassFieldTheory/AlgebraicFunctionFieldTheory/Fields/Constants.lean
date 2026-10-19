/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Perfect
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.EssentialFiniteness
import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantExtension
import Nyll.GaloisCohomology.FieldTheory.FiniteAlgebraicConstants

/-!
# Full constants and function-field degrees

The full constant field is the existing relative algebraic closure `algebraicClosure k K`.
No second constant-field type is introduced. A function-field presentation supplies
`Algebra.EssFiniteType k K`, so `FieldTheory.finite_algebraicClosure_of_finite_base` applies
when `k` is finite. Its perfectness is then the existing `PerfectField.ofFinite` instance.

The degree of this constant field over `k` is positive and divides every residue-field degree
and every divisor degree computed over `k`. These statements keep track of the change from
base-field degrees to full-constant-field degrees, needed when normalizing global degree maps.
-/

namespace FunctionField

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

section Presentation

variable [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- A finite rational-function-field extension is essentially of finite type over its base. -/
theorem essFiniteType : Algebra.EssFiniteType k K := by
  have : Algebra.EssFiniteType (Polynomial k) (RatFunc k) :=
    Algebra.EssFiniteType.of_isLocalization (RatFunc k) (nonZeroDivisors (Polynomial k))
  have : Algebra.EssFiniteType k (RatFunc k) :=
    Algebra.EssFiniteType.comp k (Polynomial k) (RatFunc k)
  have : Algebra.EssFiniteType (RatFunc k) K :=
    Algebra.EssFiniteType.of_finiteType (RatFunc k) K
  exact Algebra.EssFiniteType.comp k (RatFunc k) K

/-- The degree of the full constant field is a positive, finite normalization factor. -/
theorem fullConstants_degree_pos : 0 < Module.finrank k (algebraicClosure k K) := by
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Module.Finite k (algebraicClosure k K) :=
    FieldTheory.finite_algebraic_subextension k (algebraicClosure k K) K
  exact Module.finrank_pos

end Presentation

variable {k K}

/-- Every place degree over the base field is divisible by the degree of the full constants. -/
theorem fullConstants_degree_dvd_place_degree (v : AlgebraicCurve.Place k K) :
    Module.finrank k (algebraicClosure k K) ∣ v.deg := by
  refine ⟨(v.extendConstants (algebraicClosure k K)).deg, ?_⟩
  exact AlgebraicCurve.Place.deg_forgetConstants (K := k)
    (v.extendConstants (algebraicClosure k K))

/-- The full constant-field degree divides the degree of every divisor, including signed ones. -/
theorem fullConstants_degree_dvd_divisor_degree (D : AlgebraicCurve.Divisor k K) :
    (Module.finrank k (algebraicClosure k K) : ℤ) ∣ AlgebraicCurve.Divisor.degree D := by
  rw [AlgebraicCurve.Divisor.degree, Finsupp.liftAddHom_apply]
  apply Finset.dvd_sum
  intro v _
  change (Module.finrank k (algebraicClosure k K) : ℤ) ∣ D v * (v.deg : ℤ)
  exact dvd_mul_of_dvd_right
    (Int.natCast_dvd_natCast.mpr (fullConstants_degree_dvd_place_degree v)) (D v)

end FunctionField

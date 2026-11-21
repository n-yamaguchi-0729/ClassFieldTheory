/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.FinitePlaceContraction

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# Norm of a fractional-ideal exponent vector

A finite prime of an extension contracts to a finite prime of the base.
The norm sends its exponent to the prime below, multiplied by the inertia
degree. The resulting map on finitely supported exponent vectors is additive.
-/



@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The relative ideal norm on formal finite-prime exponent vectors. The
coefficient at an upstairs prime is transferred to its contracted prime and
multiplied by the inertia degree. -/
def fractionalIdealNormExponentMap
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    (HeightOneSpectrum (𝓞 L) →₀ ℤ) →+
      (HeightOneSpectrum (𝓞 K) →₀ ℤ) :=
  Finsupp.liftAddHom fun W =>
    (Finsupp.singleAddHom (_root_.finitePlaceBelow (K := K) W)).comp
      (AddMonoidHom.mulLeft (W.asIdeal.inertiaDeg (𝓞 K) : ℤ))


open scoped Classical in
/-- The norm transfers each exponent to the prime below with inertia-degree weight. -/
theorem fractionalIdealNormExponentMap_apply
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (e : HeightOneSpectrum (𝓞 L) →₀ ℤ) (w : HeightOneSpectrum (𝓞 K)) :
    fractionalIdealNormExponentMap K L e w =
      e.sum fun W n => if _root_.finitePlaceBelow (K := K) W = w then
        (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) * n else 0 := by
  simp only [fractionalIdealNormExponentMap, Finsupp.liftAddHom_apply,
    AddMonoidHom.coe_comp, AddMonoidHom.coe_mulLeft, Finsupp.sum_apply,
    Function.comp_apply, Finsupp.singleAddHom_apply, Finsupp.single_apply, eq_comm]

end ClassFieldTheory

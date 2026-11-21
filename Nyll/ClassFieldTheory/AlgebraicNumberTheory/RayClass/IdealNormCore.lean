/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
public import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassIdealNorm
public import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.FractionalIdealNormExponentMap
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Ideal norms and prime-to support

The ordinary ideal norm depends only on the inverse image of the finite
support of a modulus. Local higher-unit depths belong to the separate
idèle norm comparison in `RayClass.IdealNorm`.
-/

@[expose] public section

universe u v

open scoped BigOperators NumberField
open ClassFieldTheory
open NumberField IsDedekindDomain

noncomputable section

namespace RayClass

variable {K : Type u} {L : Type v}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The exponent pushforward can equivalently be written as the finite
sum over the primes above one fixed base prime. -/
theorem idealNormExponentMap_apply_eq_sum_above
    (e : HeightOneSpectrum (𝓞 L) →₀ ℤ)
    (v : HeightOneSpectrum (𝓞 K))
    [Fintype {W : HeightOneSpectrum (𝓞 L) //
      _root_.finitePlaceBelow (K := K) W = v}] :
    ClassFieldTheory.fractionalIdealNormExponentMap K L e v =
      ∑ W : {W : HeightOneSpectrum (𝓞 L) //
          _root_.finitePlaceBelow (K := K) W = v},
        (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) * e W.1 := by
  classical
  let p : HeightOneSpectrum (𝓞 L) → Prop :=
    fun W => _root_.finitePlaceBelow (K := K) W = v
  let eAbove : {W : HeightOneSpectrum (𝓞 L) // p W} →₀ ℤ :=
    e.subtypeDomain p
  rw [ClassFieldTheory.fractionalIdealNormExponentMap_apply]
  calc
    e.sum
          (fun W n =>
            if _root_.finitePlaceBelow (K := K) W = v then
              (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) * n
            else 0) =
    eAbove.sum
          (fun W n =>
            (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) * n) := by
      simp only [eAbove, p, Finsupp.sum, Finsupp.support_subtypeDomain,
        Finsupp.subtypeDomain_apply]
      calc
        (∑ W ∈ e.support,
            if _root_.finitePlaceBelow (K := K) W = v then
              (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) * e W
            else 0) =
            ∑ W ∈ e.support.filter
              (fun W => _root_.finitePlaceBelow (K := K) W = v),
              (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) * e W :=
          (Finset.sum_filter _ _).symm
        _ =
            ∑ W ∈ Finset.subtype
              (fun W => _root_.finitePlaceBelow (K := K) W = v)
              e.support,
              (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) * e W.1 :=
          (Finset.sum_subtype_eq_sum_filter
            (fun W => (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) * e W)).symm
    _ =
        ∑ W : {W : HeightOneSpectrum (𝓞 L) //
            _root_.finitePlaceBelow (K := K) W = v},
          (W.1.asIdeal.inertiaDeg (𝓞 K) : ℤ) * e W.1 := by
      rw [Finsupp.sum_fintype]
      · rfl
      · intro W
        exact mul_zero _

/-- The exponent of the norm at `v` is the inertia-degree weighted
pushforward of the upstairs prime exponents. -/
theorem count_fractionalIdealNorm
    (I : NumberFieldFractionalIdealGroup L)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
        (ClassFieldTheory.fractionalIdealNorm K L I :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      ClassFieldTheory.fractionalIdealNormExponentMap K L
        (NumberFieldFractionalIdealGroup.countVector I) v := by
  rw [ClassFieldTheory.fractionalIdealNormExponentMap_apply]
  exact ClassFieldTheory.fractionalIdealNorm_count K L I v

/-- The ideal-norm domain is determined only by primes above the base support. -/
def primeToModulusIdealNormDomain (m : Modulus K) :
    Subgroup (NumberFieldFractionalIdealGroup L) :=
  ClassFieldTheory.rayClassPrimeToIdealNormDomain K L
    { finitePart := m.finitePart, infinitePart := m.infinitePart }

/-- The ideal norm restricted to its canonical prime-to support domain. -/
noncomputable def primeToModulusIdealNorm (m : Modulus K) :
    primeToModulusIdealNormDomain (L := L) m →* primeToModulusIdeals m :=
  ClassFieldTheory.rayClassPrimeToIdealNorm K L
    { finitePart := m.finitePart, infinitePart := m.infinitePart }

/-- Forgetting the support restriction recovers the fractional-ideal norm. -/
@[simp]
theorem primeToModulusIdealNorm_coe
    (m : Modulus K) (I : primeToModulusIdealNormDomain (L := L) m) :
    (primeToModulusIdealNorm (L := L) m I : NumberFieldFractionalIdealGroup K) =
      ClassFieldTheory.fractionalIdealNorm K L (I : NumberFieldFractionalIdealGroup L) :=
  rfl

/-- The genuine norm-defined subgroup
`N_{L/K} J_L^m P_K^m` of ideals prime to `m`. -/
noncomputable def idealNormSubgroup
    (m : Modulus K) :
    Subgroup (primeToModulusIdeals m) :=
  (primeToModulusIdealNorm
    (K := K) (L := L) m).range ⊔
      principalRayIdealSubgroup m


end RayClass

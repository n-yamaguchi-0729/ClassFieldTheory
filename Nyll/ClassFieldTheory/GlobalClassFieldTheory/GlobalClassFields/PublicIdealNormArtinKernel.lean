/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Algebra.FractionalIdealFactorization
import Nyll.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.ArithmeticFrobeniusOrder
import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassIdealNorm
import Nyll.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityData
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.FinitePlaceContraction

/-!
# Ideal norms lie in the normalized Artin kernel

The forward inclusion of the ideal-theoretic norm-kernel formula follows
prime by prime.  The reverse inclusion needs a separate approximation
argument and is not asserted here.
-/

open scoped NumberField IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

universe u v

namespace ClassFieldTheory.GlobalClassFieldComparison

private theorem fractionalIdealNorm_prime
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (W : HeightOneSpectrum (𝓞 L)) :
    fractionalIdealNorm K L (finitePrimeFractionalIdeal W) =
      finitePrimeFractionalIdeal (_root_.finitePlaceBelow (K := K) W) ^
        (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) := by
  classical
  apply NumberFieldFractionalIdealGroup.ext_count
  intro v
  rw [fractionalIdealNorm_count]
  have hcount : NumberFieldFractionalIdealGroup.countVector
      (finitePrimeFractionalIdeal W) = Finsupp.single W 1 := by
    ext V
    rw [NumberFieldFractionalIdealGroup.countVector_apply]
    change FractionalIdeal.count L V
      (W.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) = _
    classical
    simp only [FractionalIdeal.count_maximal, Finsupp.single_apply]
  rw [hcount]
  change (Finsupp.single W (1 : ℤ)).sum
      (fun U n => if _root_.finitePlaceBelow (K := K) U = v then
        (U.asIdeal.inertiaDeg (𝓞 K) : ℤ) * n else 0) =
      FractionalIdeal.count K v
        ((finitePrimeFractionalIdeal (_root_.finitePlaceBelow (K := K) W) ^
          (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) :
          NumberFieldFractionalIdealGroup K) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  rw [Finsupp.sum_single_index]
  · rw [Units.val_zpow_eq_zpow_val, FractionalIdeal.count_zpow]
    change (if _root_.finitePlaceBelow (K := K) W = v then
      (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) * 1 else 0) =
      (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
        FractionalIdeal.count K v
          ((_root_.finitePlaceBelow (K := K) W).asIdeal :
            FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    classical
    rw [FractionalIdeal.count_maximal]
    split_ifs with h
    · simp only [mul_one]
    · simp only [mul_zero]
  · split_ifs <;> simp only [mul_zero]

/-- Every ideal norm prime to a modulus is killed by the Frobenius-normalized
Artin map. This is the forward half of the ideal-theoretic norm-kernel
formula, with no idèle norm substituted for an ideal norm. -/
theorem idealNormImage_le_finiteAbelianReciprocityArtinKer
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (D : FiniteAbelianReciprocityData K L) :
    rayClassIdealNormImage K L D.modulus ≤ D.artin.ker := by
  let S : Set (HeightOneSpectrum (𝓞 L)) :=
    {W | _root_.finitePlaceBelow (K := K) W ∈ D.modulus.finitePart.support}
  have hzero : D.artin.comp (rayClassIdealNorm K L D.modulus) = 1 := by
    apply FractionalIdealFactorization.primeTo_hom_ext S
    intro W hW
    let J := FractionalIdealFactorization.primeToPrime (F := L) S W hW
    let v := _root_.finitePlaceBelow (K := K) W
    have hv : v ∉ D.modulus.finitePart.support := hW
    have hw : W.asIdeal.LiesOver v.asIdeal := by
      change W.asIdeal.LiesOver (W.asIdeal.under (𝓞 K))
      infer_instance
    have hunram : Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal :=
      (D.unramifiedOutsideModulus.1 v hv) W.asIdeal inferInstance hw
    have horder := ClassFieldTheory.orderOf_arithmeticFrobeniusAt_eq_inertiaDegree
      v W hw hunram
    change D.artin (rayClassIdealNorm K L D.modulus
      J) = 1
    have hprime : (J :
        NumberFieldFractionalIdealGroup L) = finitePrimeFractionalIdeal W := rfl
    change D.artin (QuotientGroup.mk'
      (rayPrincipalIdealSubgroupInPrimeTo D.modulus)
      (rayClassPrimeToIdealNorm K L D.modulus
        J)) = 1
    have hnorm :
        (rayClassPrimeToIdealNorm K L D.modulus
          J :
          NumberFieldFractionalIdealGroup K) =
        finitePrimeFractionalIdeal v ^
          (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) := by
      change fractionalIdealNorm K L
        (J :
          NumberFieldFractionalIdealGroup L) = _
      rw [hprime]
      exact fractionalIdealNorm_prime K L W
    have hclass : QuotientGroup.mk'
        (rayPrincipalIdealSubgroupInPrimeTo D.modulus)
        (rayClassPrimeToIdealNorm K L D.modulus
          J) =
        rayClassOfFinitePrime D.modulus v hv ^
          (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) := by
      let p : rayClassPrimeToIdeals D.modulus :=
        ⟨finitePrimeFractionalIdeal v, by
          intro w hw
          exact FractionalIdeal.count_maximal_coprime K w
            (fun h => hv (h ▸ hw))⟩
      have hp : QuotientGroup.mk'
          (rayPrincipalIdealSubgroupInPrimeTo D.modulus) p =
          rayClassOfFinitePrime D.modulus v hv := rfl
      calc
        _ = QuotientGroup.mk'
              (rayPrincipalIdealSubgroupInPrimeTo D.modulus)
              (p ^ (W.asIdeal.inertiaDeg (𝓞 K) : ℤ)) := by
            congr 1
            apply Subtype.ext
            exact hnorm
        _ = (QuotientGroup.mk'
              (rayPrincipalIdealSubgroupInPrimeTo D.modulus) p) ^
              (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) :=
            map_zpow
              (QuotientGroup.mk'
                (rayPrincipalIdealSubgroupInPrimeTo D.modulus))
              p (W.asIdeal.inertiaDeg (𝓞 K) : ℤ)
        _ = _ := by rw [hp]
    rw [hclass, map_zpow, D.artin_frobenius v hv W hw]
    rw [← horder]
    simp only [zpow_natCast, pow_orderOf_eq_one]
  intro x hx
  obtain ⟨I, rfl⟩ := hx
  exact DFunLike.congr_fun hzero I

end ClassFieldTheory.GlobalClassFieldComparison

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.InfiniteOnePlaceBaseNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.OnePlaceBaseNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.IdeleClassNorm
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteLocalGlobalArtinCompatibility
public import Nyll.ClassFieldTheory.KroneckerWeber.RationalCyclotomicArithmeticReciprocity
public import Nyll.ClassFieldTheory.LocalFieldTheory.Padic.Cyclotomic.Unramified.CanonicalExtension
public import Mathlib.Topology.Instances.ZMod

/-! # Large local orders in finite quotients of the idele class group -/

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain KroneckerWeber GlobalClassFieldTheory.Reciprocity
open AlgebraicNumberTheory.Valuations
open scoped NumberField Cyclotomic

namespace ClassFieldTheory.Brauer

/-- The arithmetic reciprocity character on an actual rational cyclotomic level. -/
def rationalCyclotomicIdeleClassCharacter (m : ℕ+) :
    NumberField.IdeleClassGroup (𝓞 ℚ) ℚ →ₜ* (ZMod (m : ℕ))ˣ := by
  let E := KummerTheory.rationalCyclotomicLevel m
  let : NeZero (m : ℕ) := ⟨m.pos.ne'⟩
  let : NumberField E := KummerTheory.rationalCyclotomicLevel_numberField m
  let : IsAbelianGalois ℚ E := IsCyclotomicExtension.isAbelianGalois {(m : ℕ)} ℚ E
  let e := IsCyclotomicExtension.Rat.galEquivZMod (m : ℕ) E
  let A := arithmeticGlobalNormResidueMonoidHom ℚ E
  exact ⟨e.toMonoidHom.comp A,
    (continuous_of_discreteTopology (f := e)).comp
      (arithmeticGlobalNormResidueMonoidHom_continuous ℚ E)⟩

/-- Pull a rational cyclotomic character back along the actual idele class norm. -/
def cyclotomicIdeleClassCharacter
    (K : Type*) [Field K] [NumberField K] (m : ℕ+) :
    NumberField.IdeleClassGroup (𝓞 K) K →ₜ* (ZMod (m : ℕ))ˣ :=
  (rationalCyclotomicIdeleClassCharacter m).comp
    (NumberField.IdeleClassGroup.normContinuousMonoidHom ℚ K)

/-- Every real negative-one coordinate has the same rational cyclotomic norm value. -/
theorem cyclotomicIdeleClassCharacter_real_neg_one
    (K : Type*) [Field K] [NumberField K] (m : ℕ+) (v : InfinitePlace K) (hv : v.IsReal) :
    cyclotomicIdeleClassCharacter K m (IdeleGroup.infinitePlaceIdeleClass v (-1 : v.Completionˣ)) =
      rationalCyclotomicIdeleClassCharacter m
        (IdeleGroup.infinitePlaceIdeleClass Rat.infinitePlace
          (-1 : Rat.infinitePlace.Completionˣ)) := by
  change rationalCyclotomicIdeleClassCharacter m
    (ideleClassNorm ℚ K (IdeleGroup.infinitePlaceIdeleClass v (-1 : v.Completionˣ))) = _
  rw [IdeleGroup.ideleClassNorm_infinitePlaceIdeleClass_neg_one_of_isReal v hv,
    Subsingleton.elim (infinitePlaceBelow (K := ℚ) v) Rat.infinitePlace]

/-- The negative-one class acts nontrivially on the actual rational fourth-root field. -/
theorem rationalCyclotomicIdeleClassCharacter_complexification_neg_one_ne_one :
    rationalCyclotomicIdeleClassCharacter rationalComplexificationCyclotomicOrder
      (IdeleGroup.infinitePlaceIdeleClass Rat.infinitePlace
        (-1 : Rat.infinitePlace.Completionˣ)) ≠ 1 := by
  let m := rationalComplexificationCyclotomicOrder
  let E := rationalComplexificationCyclotomicField
  let : NeZero (m : ℕ) := ⟨m.pos.ne'⟩
  let : NumberField E := KummerTheory.rationalCyclotomicLevel_numberField m
  let : IsAbelianGalois ℚ E := IsCyclotomicExtension.isAbelianGalois {(m : ℕ)} ℚ E
  let e := IsCyclotomicExtension.Rat.galEquivZMod (m : ℕ) E
  intro h
  change e (arithmeticGlobalNormResidueMonoidHom ℚ E
    (IdeleGroup.infinitePlaceIdeleClass Rat.infinitePlace
      (-1 : Rat.infinitePlace.Completionˣ))) = 1 at h
  rw [← map_one e] at h
  have hArtin := e.injective h
  have hcomp := DFunLike.congr_fun
    (globalNormResidueMonoidHom_comp_infinitePlaceIdeleClass (K := ℚ) (L := E) Rat.infinitePlace)
    (-1 : Rat.infinitePlace.Completionˣ)
  rw [MonoidHom.comp_apply] at hcomp
  rw [arithmeticGlobalNormResidueMonoidHom_apply, inv_eq_one, hcomp] at hArtin
  exact chosenInfinitePlaceArtinMonoidHom_neg_one_ne_one_of_ramified Rat.infinitePlace
    rationalComplexification_chosenInfinitePlace_isRamified hArtin

private theorem finitePlaceIdeleClass_cast_rationalUniformizer
    (q : Nat.Primes) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : RayClass.rationalPrime q = v) :
    IdeleGroup.finitePlaceIdeleClass v
      (cast (congrArg (fun w : HeightOneSpectrum (𝓞 ℚ) => (w.adicCompletion ℚ)ˣ) hv)
        (rationalPrimeUniformizerLocalInput q)) =
      IdeleGroup.finitePlaceIdeleClass (RayClass.rationalPrime q)
        (rationalPrimeUniformizerLocalInput q) := by
  subst v
  rfl

/-- Every finite place has a one-place idele whose image in a finite cyclotomic
quotient has any prescribed positive order. The exponent of the rational Frobenius
is chosen to absorb the degree of the actual local extension over `ℚ`. -/
theorem exists_cyclotomicIdeleClassCharacter_local_order
    (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) :
    ∃ (m : ℕ+) (a : (v.adicCompletion K)ˣ),
      orderOf (cyclotomicIdeleClassCharacter K m (IdeleGroup.finitePlaceIdeleClass v a)) = n := by
  let w := finitePlaceBelow (K := ℚ) v
  let q := Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w
  have hw : RayClass.rationalPrime q = w := (Rat.HeightOneSpectrum.primesEquiv
    (R := 𝓞 ℚ)).symm_apply_apply w
  let d := IdeleGroup.finitePlaceCompletionDegree (K := ℚ) (L := K) v
  have hd : 0 < d := IdeleGroup.finitePlaceCompletionDegree_pos (K := ℚ) (L := K) v
  let f := d * n
  have hf : 0 < f := Nat.mul_pos hd hn
  let m : ℕ+ := ⟨q.1 ^ f - 1, Nat.sub_pos_of_lt (Nat.one_lt_pow hf.ne' q.2.one_lt)⟩
  let : Fact (Nat.Prime q.1) := ⟨q.2⟩
  let : NeZero (m : ℕ) := ⟨m.pos.ne'⟩
  have hcop : q.1.Coprime (m : ℕ) := prime_coprime_pow_sub_one q.1 f hf
  let u : (w.adicCompletion ℚ)ˣ :=
    cast (congrArg (fun w : HeightOneSpectrum (𝓞 ℚ) => (w.adicCompletion ℚ)ˣ) hw)
      (rationalPrimeUniformizerLocalInput q)
  let a := IdeleGroup.finitePlaceBaseUnitExtension (K := ℚ) (L := K) v u
  refine ⟨m, a, ?_⟩
  have hnorm : ideleClassNorm ℚ K (IdeleGroup.finitePlaceIdeleClass v a) =
      IdeleGroup.finitePlaceIdeleClass w (u ^ d) := by
    rw [← IdeleGroup.toStandardClass_finitePlaceIdele v a,
      ← IdeleGroup.toStandardClass_finitePlaceIdele w (u ^ d),
      ideleClassNorm_mk, IdeleGroup.norm_finitePlaceIdele_finitePlaceBaseUnitExtension]
  let E := KummerTheory.rationalCyclotomicLevel m
  let : NumberField E := KummerTheory.rationalCyclotomicLevel_numberField m
  let : IsAbelianGalois ℚ E := IsCyclotomicExtension.isAbelianGalois {(m : ℕ)} ℚ E
  let e := IsCyclotomicExtension.Rat.galEquivZMod (m : ℕ) E
  let A := arithmeticGlobalNormResidueMonoidHom ℚ E
  change orderOf (e (A (ideleClassNorm ℚ K (IdeleGroup.finitePlaceIdeleClass v a)))) = n
  rw [hnorm, map_pow, finitePlaceIdeleClass_cast_rationalUniformizer q w hw, map_pow, map_pow]
  have hFrob : e (A (IdeleGroup.finitePlaceIdeleClass (RayClass.rationalPrime q)
      (rationalPrimeUniformizerLocalInput q))) = ZMod.unitOfCoprime q.1 hcop :=
    rationalCyclotomicLevel_arithmeticGlobalNormResidue_at_unramifiedPrime
      (m : ℕ) q (q.2.coprime_iff_not_dvd.mp hcop)
  rw [hFrob]
  have horder : orderOf (ZMod.unitOfCoprime q.1 hcop) = f :=
    padicCyclotomicUnramifiedResidueDegree_prime_pow_sub_one q.1 f hf
  have hdiv : d ∣ orderOf (ZMod.unitOfCoprime q.1 hcop) := by
    rw [horder]
    exact dvd_mul_right d n
  rw [orderOf_pow_of_dvd hd.ne' hdiv, horder]
  exact Nat.mul_div_cancel_left n hd

end ClassFieldTheory.Brauer

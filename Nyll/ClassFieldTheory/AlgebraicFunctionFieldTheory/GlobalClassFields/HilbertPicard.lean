/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.PointedPicard
public import Nyll.ClassFieldTheory.Algebra.RestrictedProduct.Valuation
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Divisor
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.IntegralUnits
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.HilbertClassFieldConstruction
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.SplitRayQuotient
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteAbelian
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
public import Mathlib.FieldTheory.Galois.Basic

/-!
# The actual Hilbert class field and the degree-zero Picard group

The pointed divisor-class map has precisely the original zero-modulus ray
kernel together with the local group at the chosen degree-one place. Thus
finite reciprocity identifies the actual Hilbert Galois group with `Pic0`.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [HasPrincipalDivisors k K]

local instance : CommGroup (IdeleClassGroup k K) :=
  QuotientGroup.Quotient.commGroup (G := IdeleGroup k K) (IdeleGroup.principalSubgroup k K)

local instance : IsMulCommutative (IdeleClassGroup k K) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

namespace IdeleClassGroup

/-- Remove the degree of the actual idele divisor class at the specified place. -/
def pointedDivisorClass (ε : Place k K) (hε : ε.deg = 1) :
    IdeleClassGroup k K →* Multiplicative (Pic0 k K) :=
  (Pic0.pointedClass ε hε).toMultiplicative.comp divisorClass

theorem pointedDivisorClass_surjective (ε : Place k K) (hε : ε.deg = 1) :
    Function.Surjective (pointedDivisorClass ε hε) := by
  intro a
  obtain ⟨c, hc⟩ := Pic0.pointedClass_surjective ε hε a.toAdd
  obtain ⟨b, hb⟩ := divisorClass_surjective (k := k) (K := K) (Multiplicative.ofAdd c)
  refine ⟨b, ?_⟩
  change Multiplicative.ofAdd (Pic0.pointedClass ε hε (divisorClass b).toAdd) = a
  rw [hb]
  exact congrArg Multiplicative.ofAdd hc

theorem pointedDivisorClass_placeIdele
    (ε : Place k K) (hε : ε.deg = 1) (v : Place k K) (a : v.adicCompletionˣ) :
    pointedDivisorClass ε hε (mk (IdeleGroup.placeIdele v a)) =
      Multiplicative.ofAdd (Pic0.pointedClass ε hε
        (H1Gm.mk (Finsupp.single v (IdeleGroup.localOrder v a).toAdd))) := by
  change Multiplicative.ofAdd (Pic0.pointedClass ε hε
    (H1Gm.mk (IdeleGroup.divisor (IdeleGroup.placeIdele v a)).toAdd)) = _
  rw [IdeleGroup.divisor_placeIdele, toAdd_ofAdd]

/-- The exact native kernel, including the degree direction killed at the
chosen place. Its reverse inclusion uses an actual local element of the
required order, not an abstract degree-splitting assumption. -/
theorem pointedDivisorClass_ker (ε : Place k K) (hε : ε.deg = 1) :
    (pointedDivisorClass ε hε).ker = RayClass.splitRaySubgroup 0 {ε} := by
  classical
  apply le_antisymm
  · intro c hc
    change Pic0.pointedClass ε hε (divisorClass c).toAdd = 0 at hc
    have hcclass := (Pic0.pointedClass_eq_zero_iff ε hε (divisorClass c).toAdd).mp hc
    let n : ℤ := H1Gm.degree k K (divisorClass c).toAdd
    let a : ε.adicCompletionˣ :=
      RestrictedProduct.DiscreteValuation.chosenLocalOrderSection ε.adicCompletion
        (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective K
          ε.heightOneSpectrum) n
    have ha : (IdeleGroup.localOrder ε a).toAdd = n :=
      RestrictedProduct.DiscreteValuation.localOrder_chosenLocalOrderSection
        ε.adicCompletion _ n
    let d : IdeleClassGroup k K := mk (IdeleGroup.placeIdele ε a)
    have hdclass : divisorClass d =
        Multiplicative.ofAdd (H1Gm.mk (Finsupp.single ε n)) := by
      change Multiplicative.ofAdd
        (H1Gm.mk (IdeleGroup.divisor (IdeleGroup.placeIdele ε a)).toAdd) = _
      rw [IdeleGroup.divisor_placeIdele, ha, toAdd_ofAdd]
    have hclass : divisorClass c = divisorClass d := by
      rw [hdclass]
      exact congrArg Multiplicative.ofAdd hcclass
    have hunit : c / d ∈ RayClass.rayClassSubgroup (0 : RayClass.Modulus k K) := by
      rw [RayClass.rayClassSubgroup, RayClass.congruenceSubgroup_zero]
      change c / d ∈ integralSubgroup
      rw [← divisorClass_ker]
      change divisorClass (c / d) = 1
      rw [map_div, hclass, div_self']
    have hd : d ∈ RayClass.splitRaySubgroup 0 {ε} :=
      RayClass.placeIdele_mem_splitRaySubgroup 0 {ε} (Finset.mem_singleton_self ε) a
    have hc' := (RayClass.splitRaySubgroup (k := k) (K := K) 0 {ε}).mul_mem
      ((show RayClass.rayClassSubgroup (0 : RayClass.Modulus k K) ≤
        RayClass.splitRaySubgroup 0 {ε} from le_sup_left) hunit) hd
    simpa only [div_mul_cancel] using hc'
  · rw [RayClass.splitRaySubgroup]
    apply sup_le
    · intro c hc
      have hc' : divisorClass c = 1 := by
        change c ∈ (divisorClass (k := k) (K := K)).ker
        rw [divisorClass_ker]
        rw [RayClass.rayClassSubgroup, RayClass.congruenceSubgroup_zero] at hc
        exact hc
      change (Pic0.pointedClass ε hε).toMultiplicative (divisorClass c) = 1
      rw [hc', map_one]
    · apply iSup_le
      intro v
      apply iSup_le
      intro hv
      have hvε : v = ε := Finset.mem_singleton.mp hv
      subst v
      rintro c ⟨a, rfl⟩
      change pointedDivisorClass ε hε (mk (IdeleGroup.placeIdele ε a)) = 1
      rw [pointedDivisorClass_placeIdele]
      change Pic0.pointedClass ε hε
        (H1Gm.mk (Finsupp.single ε (IdeleGroup.localOrder ε a).toAdd)) = 0
      rw [Pic0.pointedClass_eq_zero_iff, H1Gm.degree_mk, Divisor.degree_single,
        hε, Nat.cast_one, mul_one]

end IdeleClassGroup

/-- The prescribed-splitting zero-ray quotient is the actual degree-zero
Picard group. -/
def splitRayQuotientEquivPic0 (ε : Place k K) (hε : ε.deg = 1) :
    (IdeleClassGroup k K ⧸ RayClass.splitRaySubgroup 0 {ε}) ≃*
      Multiplicative (Pic0 k K) :=
  (QuotientGroup.quotientMulEquivOfEq (G := IdeleClassGroup k K)
    (IdeleClassGroup.pointedDivisorClass_ker (k := k) (K := K) ε hε).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (IdeleClassGroup.pointedDivisorClass (k := k) (K := K) ε hε)
        (IdeleClassGroup.pointedDivisorClass_surjective (k := k) (K := K) ε hε))

theorem splitRayQuotientEquivPic0_mk (ε : Place k K) (hε : ε.deg = 1)
    (c : IdeleClassGroup k K) :
    splitRayQuotientEquivPic0 ε hε (QuotientGroup.mk c) =
      IdeleClassGroup.pointedDivisorClass ε hε c := rfl

variable (k K) [Finite k] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- Finite class field theory identifies the Galois group of the actual
Hilbert class field split at a degree-one place with the original `Pic0`. -/
def hilbertClassFieldGaloisEquivPic0 (ε : Place k K) (hε : ε.deg = 1) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    Gal((hilbertClassField k K {ε} (Finset.singleton_nonempty _)).val/K) ≃*
      Multiplicative (Pic0 k K) := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  let H := hilbertClassField k K {ε} (Finset.singleton_nonempty _)
  have : HasPrincipalDivisors k H.val :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K H.val).toHasPrincipalDivisors
  exact (abelianFiniteNormQuotientEquiv k K H.val).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (hilbertClassField_norm k K {ε} (Finset.singleton_nonempty _))).trans
        (splitRayQuotientEquivPic0 ε hε))

/-- This comparison sends the actual finite Artin symbol to the pointed
class of its original idele divisor. -/
theorem hilbertClassFieldGaloisEquivPic0_artin (ε : Place k K) (hε : ε.deg = 1) :
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
        (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
    let H := hilbertClassField k K {ε} (Finset.singleton_nonempty _)
    let _ : HasPrincipalDivisors k H.val :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K H.val).toHasPrincipalDivisors
    let e : Gal(H.val/K) ≃* Multiplicative (Pic0 k K) :=
      hilbertClassFieldGaloisEquivPic0 k K ε hε
    ∀ c : IdeleClassGroup k K,
      e (abelianFiniteArtin k K H.val c) =
        IdeleClassGroup.pointedDivisorClass ε hε c := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ H hprincipal ePic c
  let e : (IdeleClassGroup k K ⧸
      (IdeleClassGroup.norm (k := k) (K := K) (L := H.val)).range) ≃* Gal(H.val/K) :=
    abelianFiniteNormQuotientEquiv k K H.val
  have he : e.symm (e (QuotientGroup.mk c)) = QuotientGroup.mk c :=
    e.symm_apply_apply (QuotientGroup.mk c)
  have hnorm : (IdeleClassGroup.norm (k := k) (K := K) (L := H.val)).range =
      RayClass.splitRaySubgroup 0 {ε} :=
    hilbertClassField_norm k K {ε} (Finset.singleton_nonempty _)
  exact (congrArg (fun q : IdeleClassGroup k K ⧸
        (IdeleClassGroup.norm (k := k) (K := K) (L := H.val)).range =>
      splitRayQuotientEquivPic0 ε hε (QuotientGroup.quotientMulEquivOfEq hnorm q)) he).trans
        ((congrArg (splitRayQuotientEquivPic0 ε hε)
          (QuotientGroup.quotientMulEquivOfEq_mk hnorm c)).trans
            (splitRayQuotientEquivPic0_mk ε hε c))

/-- The degree of the original Hilbert class field is the cardinality of
the degree-zero divisor class group. -/
theorem finrank_hilbertClassField (ε : Place k K) (hε : ε.deg = 1) :
    Module.finrank K (hilbertClassField k K {ε} (Finset.singleton_nonempty _)).val =
      Nat.card (Pic0 k K) := by
  let _ : Algebra k (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
  let _ : Algebra (RatFunc k) (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
  have hkKΩ : IsScalarTower k K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRKΩ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRΩ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
      (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
  let H := hilbertClassField k K {ε} (Finset.singleton_nonempty _)
  exact (IsGalois.card_aut_eq_finrank K H.val).symm.trans
    (Nat.card_congr (hilbertClassFieldGaloisEquivPic0 k K ε hε).toEquiv)

end FunctionField

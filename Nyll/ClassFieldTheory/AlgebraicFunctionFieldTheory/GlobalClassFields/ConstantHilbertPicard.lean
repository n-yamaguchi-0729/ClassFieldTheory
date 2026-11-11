/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.HilbertPicard
public import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantReindex
public import Nyll.ClassFieldTheory.Algebra.RestrictedProduct.Valuation
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve

/-!
# Hilbert reciprocity with the original finite base retained

The chosen place is rational over the actual enlarged constants `E`, while
the ideles, Artin map, and Hilbert class field remain over the original
finite field `k`. Reindexing the original divisor class before removing its
degree gives the exact prescribed-splitting ray kernel. This provides the
Picard comparison needed for constant towers without changing the Artin
normalization or requiring the chosen place to have degree one over `k`.
-/

@[expose] public section

noncomputable section

universe u v w

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField

variable (k : Type u) (E : Type v) (K : Type w) [Field k] [Field E] [Field K]
  [Algebra k E] [Algebra k K] [Algebra E K] [IsScalarTower k E K]
  [Algebra.IsIntegral k E] [HasPrincipalDivisors k K] [HasPrincipalDivisors E K]

local instance : CommGroup (IdeleClassGroup k K) :=
  QuotientGroup.Quotient.commGroup (G := IdeleGroup k K) (IdeleGroup.principalSubgroup k K)

local instance : IsMulCommutative (IdeleClassGroup k K) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

namespace IdeleClassGroup

/-- The original idele divisor, reindexed over its actual larger constants
and made degree zero at the specified rational place. -/
def constantPointedDivisorClass (ε : Place E K) (hε : ε.deg = 1) :
    IdeleClassGroup k K →* Multiplicative (Pic0 E K) :=
  ((Pic0.pointedClass ε hε).comp (picConstantEquiv k E K).toAddMonoidHom).toMultiplicative.comp
    divisorClass

/-- Every actual degree-zero class is obtained from original-base ideles. -/
theorem constantPointedDivisorClass_surjective (ε : Place E K) (hε : ε.deg = 1) :
    Function.Surjective (constantPointedDivisorClass k E K ε hε) := by
  intro a
  obtain ⟨c, hc⟩ := Pic0.pointedClass_surjective ε hε a.toAdd
  obtain ⟨d, hd⟩ := (picConstantEquiv k E K).surjective c
  obtain ⟨b, hb⟩ := divisorClass_surjective (k := k) (K := K) (Multiplicative.ofAdd d)
  refine ⟨b, ?_⟩
  change Multiplicative.ofAdd
    (Pic0.pointedClass ε hε (picConstantEquiv k E K (divisorClass b).toAdd)) = a
  rw [hb, toAdd_ofAdd, hd]
  exact congrArg Multiplicative.ofAdd hc

/-- The original local idele at the same place gives its reindexed class. -/
theorem constantPointedDivisorClass_placeIdele
    (ε : Place E K) (hε : ε.deg = 1) (v : Place k K) (a : v.adicCompletionˣ) :
    constantPointedDivisorClass k E K ε hε (mk (IdeleGroup.placeIdele v a)) =
      Multiplicative.ofAdd (Pic0.pointedClass ε hε
        (H1Gm.mk (Finsupp.single (v.extendConstants E) (IdeleGroup.localOrder v a).toAdd))) := by
  change Multiplicative.ofAdd (Pic0.pointedClass ε hε
    (picConstantEquiv k E K (H1Gm.mk (IdeleGroup.divisor (IdeleGroup.placeIdele v a)).toAdd))) = _
  rw [IdeleGroup.divisor_placeIdele, toAdd_ofAdd, picConstantEquiv_mk,
    divisorConstantEquiv_single]

/-- Its kernel is the original-base zero-ray subgroup split at the same
place. No degree-one hypothesis over the smaller constants is used. -/
theorem constantPointedDivisorClass_ker (ε : Place E K) (hε : ε.deg = 1) :
    (constantPointedDivisorClass k E K ε hε).ker =
      RayClass.splitRaySubgroup 0 {ε.forgetConstants (K := k)} := by
  classical
  let v := ε.forgetConstants (K := k)
  have hv : v.extendConstants E = ε := (Place.constantFieldEquiv k E).apply_symm_apply ε
  apply le_antisymm
  · intro c hc
    change Pic0.pointedClass ε hε (picConstantEquiv k E K (divisorClass c).toAdd) = 0 at hc
    have hcclass := (Pic0.pointedClass_eq_zero_iff ε hε
      (picConstantEquiv k E K (divisorClass c).toAdd)).mp hc
    let n : ℤ := H1Gm.degree E K (picConstantEquiv k E K (divisorClass c).toAdd)
    let a : v.adicCompletionˣ :=
      RestrictedProduct.DiscreteValuation.chosenLocalOrderSection v.adicCompletion
        (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective K
          v.heightOneSpectrum) n
    have ha : (IdeleGroup.localOrder v a).toAdd = n :=
      RestrictedProduct.DiscreteValuation.localOrder_chosenLocalOrderSection
        v.adicCompletion _ n
    let d : IdeleClassGroup k K := mk (IdeleGroup.placeIdele v a)
    have hdclass : divisorClass d = Multiplicative.ofAdd (H1Gm.mk (Finsupp.single v n)) := by
      change Multiplicative.ofAdd
        (H1Gm.mk (IdeleGroup.divisor (IdeleGroup.placeIdele v a)).toAdd) = _
      rw [IdeleGroup.divisor_placeIdele, ha, toAdd_ofAdd]
    have hclass : divisorClass c = divisorClass d := by
      apply Multiplicative.ext
      apply (picConstantEquiv k E K).injective
      rw [hdclass, toAdd_ofAdd, picConstantEquiv_mk, divisorConstantEquiv_single, hv]
      exact hcclass
    have hunit : c / d ∈ RayClass.rayClassSubgroup (0 : RayClass.Modulus k K) := by
      rw [RayClass.rayClassSubgroup, RayClass.congruenceSubgroup_zero]
      change c / d ∈ integralSubgroup
      rw [← divisorClass_ker]
      change divisorClass (c / d) = 1
      rw [map_div, hclass, div_self']
    have hd : d ∈ RayClass.splitRaySubgroup 0 {v} :=
      RayClass.placeIdele_mem_splitRaySubgroup 0 {v} (Finset.mem_singleton_self v) a
    have h := (RayClass.splitRaySubgroup (k := k) (K := K) 0 {v}).mul_mem
      ((show RayClass.rayClassSubgroup (0 : RayClass.Modulus k K) ≤
        RayClass.splitRaySubgroup 0 {v} from le_sup_left) hunit) hd
    simpa only [div_mul_cancel] using h
  · rw [RayClass.splitRaySubgroup]
    apply sup_le
    · intro c hc
      have hc' : divisorClass c = 1 := by
        change c ∈ (divisorClass (k := k) (K := K)).ker
        rw [divisorClass_ker]
        rw [RayClass.rayClassSubgroup, RayClass.congruenceSubgroup_zero] at hc
        exact hc
      change Multiplicative.ofAdd
        (Pic0.pointedClass ε hε (picConstantEquiv k E K (divisorClass c).toAdd)) = 1
      rw [hc']
      change Multiplicative.ofAdd (Pic0.pointedClass ε hε (picConstantEquiv k E K 0)) = 1
      rw [map_zero, map_zero]
      rfl
    · apply iSup_le
      intro w
      apply iSup_le
      intro hw
      have hwv : w = v := Finset.mem_singleton.mp hw
      subst w
      rintro c ⟨a, rfl⟩
      change constantPointedDivisorClass k E K ε hε (mk (IdeleGroup.placeIdele v a)) = 1
      rw [constantPointedDivisorClass_placeIdele, hv]
      change Pic0.pointedClass ε hε
        (H1Gm.mk (Finsupp.single ε (IdeleGroup.localOrder v a).toAdd)) = 0
      rw [Pic0.pointedClass_eq_zero_iff, H1Gm.degree_mk, Divisor.degree_single,
        hε, Nat.cast_one, mul_one]

end IdeleClassGroup

/-- The original-base split ray quotient is the Picard group measured over
the actual enlarged constants. -/
def constantSplitRayQuotientEquivPic0 (ε : Place E K) (hε : ε.deg = 1) :
    (IdeleClassGroup k K ⧸ RayClass.splitRaySubgroup 0 {ε.forgetConstants (K := k)}) ≃*
      Multiplicative (Pic0 E K) :=
  (QuotientGroup.quotientMulEquivOfEq
    (IdeleClassGroup.constantPointedDivisorClass_ker k E K ε hε).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (IdeleClassGroup.constantPointedDivisorClass k E K ε hε)
        (IdeleClassGroup.constantPointedDivisorClass_surjective k E K ε hε))

theorem constantSplitRayQuotientEquivPic0_mk (ε : Place E K) (hε : ε.deg = 1)
    (c : IdeleClassGroup k K) :
    constantSplitRayQuotientEquivPic0 k E K ε hε (QuotientGroup.mk c) =
      IdeleClassGroup.constantPointedDivisorClass k E K ε hε c := rfl

variable [Finite k] [Algebra (RatFunc k) K]
  [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- Actual Hilbert reciprocity, retaining the initial finite base at every
stage, identifies its Galois group with the Picard group over the stage's
own constants. -/
def constantHilbertClassFieldGaloisEquivPic0 (ε : Place E K) (hε : ε.deg = 1) :
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
    Gal((hilbertClassField k K {ε.forgetConstants (K := k)}
      (Finset.singleton_nonempty _)).val/K) ≃* Multiplicative (Pic0 E K) := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ
  let H := hilbertClassField k K {ε.forgetConstants (K := k)} (Finset.singleton_nonempty _)
  have : HasPrincipalDivisors k H.val :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K H.val).toHasPrincipalDivisors
  exact (abelianFiniteNormQuotientEquiv k K H.val).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (hilbertClassField_norm k K {ε.forgetConstants (K := k)} (Finset.singleton_nonempty _))).trans
        (constantSplitRayQuotientEquivPic0 k E K ε hε))

/-- The comparison uses the original Artin map and original idele divisor,
with only the proved constant reindexing on the Picard side. -/
theorem constantHilbertClassFieldGaloisEquivPic0_artin (ε : Place E K) (hε : ε.deg = 1) :
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
    let H := hilbertClassField k K {ε.forgetConstants (K := k)} (Finset.singleton_nonempty _)
    let _ : HasPrincipalDivisors k H.val :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K H.val).toHasPrincipalDivisors
    let e : Gal(H.val/K) ≃* Multiplicative (Pic0 E K) :=
      constantHilbertClassFieldGaloisEquivPic0 k E K ε hε
    ∀ c : IdeleClassGroup k K,
      e (abelianFiniteArtin k K H.val c) =
        IdeleClassGroup.constantPointedDivisorClass k E K ε hε c := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ H hprincipal ePic c
  let e : (IdeleClassGroup k K ⧸
      (IdeleClassGroup.norm (k := k) (K := K) (L := H.val)).range) ≃* Gal(H.val/K) :=
    abelianFiniteNormQuotientEquiv k K H.val
  have he : e.symm (e (QuotientGroup.mk c)) = QuotientGroup.mk c :=
    e.symm_apply_apply (QuotientGroup.mk c)
  have hnorm : (IdeleClassGroup.norm (k := k) (K := K) (L := H.val)).range =
      RayClass.splitRaySubgroup 0 {ε.forgetConstants (K := k)} :=
    hilbertClassField_norm k K {ε.forgetConstants (K := k)} (Finset.singleton_nonempty _)
  exact (congrArg (fun q : IdeleClassGroup k K ⧸
        (IdeleClassGroup.norm (k := k) (K := K) (L := H.val)).range =>
      constantSplitRayQuotientEquivPic0 k E K ε hε
        (QuotientGroup.quotientMulEquivOfEq hnorm q)) he).trans
          ((congrArg (constantSplitRayQuotientEquivPic0 k E K ε hε)
            (QuotientGroup.quotientMulEquivOfEq_mk hnorm c)).trans
              (constantSplitRayQuotientEquivPic0_mk k E K ε hε c))

/-- Every Hilbert automorphism has an original-base idele representative
whose reindexed divisor class is already the associated degree-zero class.
This choice allows norms to be compared without imposing a compatibility
condition on the distinguished places in different constant stages. -/
theorem exists_zeroDegree_ideleClass_artin
    (ε : Place E K) (hε : ε.deg = 1) :
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
    let H := hilbertClassField k K {ε.forgetConstants (K := k)} (Finset.singleton_nonempty _)
    let _ : HasPrincipalDivisors k H.val :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K H.val).toHasPrincipalDivisors
    ∀ σ : Gal(H.val/K), ∃ c : IdeleClassGroup k K,
      abelianFiniteArtin k K H.val c = σ ∧
        picConstantEquiv k E K (IdeleClassGroup.divisorClass c).toAdd =
          H1Gm.ofPic0 E K ((constantHilbertClassFieldGaloisEquivPic0 k E K ε hε σ).toAdd) := by
  intro akΩ aRΩ hkKΩ hRKΩ hkRΩ H hprincipal σ
  let e := constantHilbertClassFieldGaloisEquivPic0 k E K ε hε
  obtain ⟨c, hc⟩ := IdeleClassGroup.divisorClass_surjective (k := k) (K := K)
    (Multiplicative.ofAdd ((picConstantEquiv k E K).symm
      (H1Gm.ofPic0 E K (e σ).toAdd)))
  have hclass : picConstantEquiv k E K (IdeleClassGroup.divisorClass c).toAdd =
      H1Gm.ofPic0 E K (e σ).toAdd := by
    rw [hc]
    exact (picConstantEquiv k E K).apply_symm_apply _
  refine ⟨c, ?_, hclass⟩
  apply e.injective
  rw [constantHilbertClassFieldGaloisEquivPic0_artin]
  change Multiplicative.ofAdd (Pic0.pointedClass ε hε
    (picConstantEquiv k E K (IdeleClassGroup.divisorClass c).toAdd)) = e σ
  rw [hclass, Pic0.pointedClass_ofPic0, ofAdd_toAdd]

end FunctionField

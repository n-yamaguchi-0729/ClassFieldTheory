/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.ArtinSemilinear
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.ConstantHilbertPicard
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardAction
public import Nyll.AlgebraicCurves.Places.Restriction.RestrictAlongEqSmulEqInvSmulPow
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SemilinearNaturality

/-!
# Semilinear action in the original Hilbert–Picard comparison

Viewing a field automorphism as a degree-one extension identifies actual
idele base change with the original semilinear action on divisor classes.
Reindexing constants preserves that action. Applied to original Artin
reciprocity, this proves the Hilbert–Picard conjugation square whenever an
actual compatible automorphism of the Hilbert field is specified.
-/

@[expose] public section

noncomputable section

universe u v w

open AlgebraicCurve

attribute [local instance]
  SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0

namespace AlgebraicCurve.Divisor

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [HasPrincipalDivisors k K]

/-- Pullback through the actual field automorphism is its established
semilinear action on divisors; its local ramification indices are one. -/
theorem pullback_algAut (e : K ≃ₐ[k] K) :
    let aKK : Algebra K K := e.toRingHom.toAlgebra
    let _ : SMul K K := aKK.toSMul
    let _ : Module K K := aKK.toModule
    let _ : IsScalarTower k K K :=
      IsScalarTower.of_algebraMap_eq (fun a => (e.commutes a).symm)
    let _ : FiniteDimensional K K :=
      RingHom.Finite.of_surjective e.toRingHom e.surjective
    ∀ D : Divisor k K, pullback K D = SemilinearAut.ofAlgAut e • D := by
  intro aKK sKK mKK hkKK hKK D
  let g : SemilinearAut k K := SemilinearAut.ofAlgAut e
  have heIntegral : e.toAlgHom.toRingHom.IsIntegral :=
    fun x => Algebra.IsIntegral.isIntegral (R := K) x
  have hrestrict (w : Place k K) : w.restrict K = g⁻¹ • w := by
    exact Place.restrictAlong_eq_smul_of_forall_eq_inv_smul_pow
      1 one_ne_zero g⁻¹ e.toAlgHom heIntegral
      (fun x => by simp only [inv_inv, pow_one]; rfl) w
  have hramification (w : Place k K) : w.ramificationIndex K = 1 := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
    have hπne : (π : K) ≠ 0 := by
      intro h
      exact hπ.ne_zero (Subtype.ext h)
    have hne : e.symm (π : K) ≠ 0 := by
      intro h
      apply hπne
      exact e.symm.injective (h.trans (map_zero e.symm).symm)
    have hord : w.ord (algebraMap K K (e.symm (π : K))) = 1 := by
      change w.ord (e (e.symm (π : K))) = 1
      rw [e.apply_symm_apply]
      exact w.ord_coe_irreducible hπ
    have hle := w.ramificationIndex_le_ord (F := K) hne
      (show 0 < w.ord (algebraMap K K (e.symm (π : K))) by rw [hord]; exact one_pos)
    have hpos := w.ramificationIndex_pos (F := K)
    rw [hord] at hle
    omega
  apply Finsupp.ext
  intro w
  rw [pullback_apply, hramification, Nat.cast_one, one_mul, hrestrict,
    SemilinearAut.divisor_smul_apply]

end AlgebraicCurve.Divisor

namespace FunctionField

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [HasPrincipalDivisors k K]

/-- The original idele base-change map for an automorphism induces the
original semilinear action on the full Picard group. -/
theorem IdeleClassGroup.divisorClass_baseChange_algAut (e : K ≃ₐ[k] K) :
    let aKK : Algebra K K := e.toRingHom.toAlgebra
    let _ : SMul K K := aKK.toSMul
    let _ : Module K K := aKK.toModule
    let _ : IsScalarTower k K K :=
      IsScalarTower.of_algebraMap_eq (fun a => (e.commutes a).symm)
    let _ : FiniteDimensional K K :=
      RingHom.Finite.of_surjective e.toRingHom e.surjective
    ∀ c : IdeleClassGroup k K,
      (divisorClass (baseChange (k := k) (K := K) (L := K) c)).toAdd =
        SemilinearAut.ofAlgAut e • (divisorClass c).toAdd := by
  intro aKK sKK mKK hkKK hKK c
  obtain ⟨a, rfl⟩ := IdeleClassGroup.mk_surjective (k := k) (K := K) c
  change H1Gm.mk (IdeleGroup.divisor
    (IdeleGroup.baseChange (k := k) (K := K) (L := K) a)).toAdd =
      SemilinearAut.ofAlgAut e • H1Gm.mk (IdeleGroup.divisor a).toAdd
  rw [IdeleGroup.divisor_baseChange]
  change H1Gm.mk (Divisor.pullback K (IdeleGroup.divisor a).toAdd) = _
  rw [Divisor.pullback_algAut, SemilinearAut.pic_smul_mk]

variable {E : Type w} [Field E] [Algebra k E] [Algebra E K]
    [IsScalarTower k E K] [Algebra.IsIntegral k E]

omit [HasPrincipalDivisors k K] in
/-- Reindexing constants preserves the actual action on divisor classes
when the two actions have the same original field automorphism. -/
theorem picConstantEquiv_smul_of_toRingAut_eq
    (g : SemilinearAut k K) (h : SemilinearAut E K)
    (hgh : SemilinearAut.toRingAut g = SemilinearAut.toRingAut h)
    (x : Pic k K) :
    picConstantEquiv k E K (g • x) = h • picConstantEquiv k E K x := by
  have hplace (w : Place E K) :
      (h⁻¹ • w).forgetConstants (K := k) = g⁻¹ • w.forgetConstants (K := k) := by
    apply Place.ext
    ext a
    change a ∈ (h⁻¹ • w).toValuationSubring ↔
      a ∈ (g⁻¹ • w.forgetConstants (K := k)).toValuationSubring
    rw [SemilinearAut.smul_toValuationSubring, SemilinearAut.smul_toValuationSubring,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [inv_inv, SemilinearAut.smul_def]
    rw [hgh]
    rfl
  obtain ⟨D, rfl⟩ := H1Gm.mk_surjective x
  rw [SemilinearAut.pic_smul_mk, picConstantEquiv_mk, picConstantEquiv_mk,
    SemilinearAut.pic_smul_mk]
  apply congrArg H1Gm.mk
  apply Finsupp.ext
  intro w
  rw [divisorConstantEquiv_apply, SemilinearAut.divisor_smul_apply,
    SemilinearAut.divisor_smul_apply, divisorConstantEquiv_apply, hplace]

variable [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Module.Finite k E] [HasPrincipalDivisors E K]

omit [Module.Finite k E] in
/-- Conjugation by an actual compatible automorphism of the original
Hilbert field is the original semilinear Picard action. The comparison
uses actual zero-degree idele representatives and proves their compatibility. -/
theorem constantHilbertClassFieldGaloisEquivPic0_conjugation
    (ε : Place E K) (hε : ε.deg = 1) :
    let H := hilbertClassField k K {ε.forgetConstants (K := k)}
      (Finset.singleton_nonempty _)
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : Algebra (RatFunc k) (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun a =>
        congrArg (algebraMap K (SeparableClosure K))
          (IsScalarTower.algebraMap_apply k (RatFunc k) K a))
    ∀ (eK : K ≃ₐ[k] K) (g : SemilinearAut E K)
      (_ : eK.toRingEquiv = SemilinearAut.toRingAut g)
      (eH : H.val ≃ₐ[k] H.val)
      (hcomm : ∀ a : K, eH (algebraMap K H.val a) = algebraMap K H.val (eK a))
      (σ : Gal(H.val/K)),
      ((constantHilbertClassFieldGaloisEquivPic0 k E K ε hε)
        (LocalClassFieldTheory.semilinearGaloisGroupCongr K K H.val H.val
          eK.toRingEquiv eH.toRingEquiv hcomm σ)).toAdd =
        g • ((constantHilbertClassFieldGaloisEquivPic0 k E K ε hε) σ).toAdd := by
  intro H akΩ aRΩ hkKΩ hRKΩ hkRΩ eK g hfield eH hcomm σ
  have hpH : HasPrincipalDivisors k H.val :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K H.val).toHasPrincipalDivisors
  obtain ⟨c, hc, hdegree⟩ := exists_zeroDegree_ideleClass_artin k E K ε hε σ
  have hartin := abelianFiniteArtin_algEquiv_conjugation eK eH hcomm c
  let aKH : Algebra K H.val := inferInstance
  have hkKH : IsScalarTower k K H.val := inferInstance
  let conjugation := LocalClassFieldTheory.semilinearGaloisGroupCongr K K H.val H.val
    eK.toRingEquiv eH.toRingEquiv hcomm
  let aKK : Algebra K K := eK.toRingHom.toAlgebra
  let sKK : SMul K K := aKK.toSMul
  let mKK : Module K K := aKK.toModule
  have hkKK : IsScalarTower k K K :=
    IsScalarTower.of_algebraMap_eq (fun a => (eK.commutes a).symm)
  have hKK : FiniteDimensional K K :=
    RingHom.Finite.of_surjective eK.toRingHom eK.surjective
  have hconjugation : conjugation σ =
      abelianFiniteArtin k K H.val
        (IdeleClassGroup.baseChange (k := k) (K := K) (L := K) c) := by
    rw [← hc]
    exact hartin
  have hclass : picConstantEquiv k E K
      (IdeleClassGroup.divisorClass
        (IdeleClassGroup.baseChange (k := k) (K := K) (L := K) c)).toAdd =
      H1Gm.ofPic0 E K
        (g • ((constantHilbertClassFieldGaloisEquivPic0 k E K ε hε) σ).toAdd) := by
    rw [IdeleClassGroup.divisorClass_baseChange_algAut,
      picConstantEquiv_smul_of_toRingAut_eq (SemilinearAut.ofAlgAut eK) g hfield,
      hdegree, H1Gm.ofPic0_smul]
  change ((constantHilbertClassFieldGaloisEquivPic0 k E K ε hε)
    (conjugation σ)).toAdd = _
  rw [hconjugation, constantHilbertClassFieldGaloisEquivPic0_artin]
  change Pic0.pointedClass ε hε
    (picConstantEquiv k E K (IdeleClassGroup.divisorClass
      (IdeleClassGroup.baseChange (k := k) (K := K) (L := K) c)).toAdd) = _
  rw [hclass, Pic0.pointedClass_ofPic0]

end FunctionField

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.HilbertBaseChange
public import Nyll.AlgebraicCurves.Places.Restriction.RestrictAlongEqSmulEqInvSmulPow

/-!
# Restricting original ambient automorphisms to pointed Hilbert fields

The degree-one case of actual Hilbert base change gives covariance under
field isomorphisms. Applying it to an ambient automorphism and its inverse
proves stability of the Hilbert field at a fixed place. The resulting
automorphism is the literal restriction through the original embedding.
-/

@[expose] public section

noncomputable section

universe u v w x

open AlgebraicCurve

namespace FunctionField

private theorem restrict_algAut
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] (e : K ≃ₐ[k] K) :
    let aKK : Algebra K K := e.toRingHom.toAlgebra
    let _ : SMul K K := aKK.toSMul
    let _ : Module K K := aKK.toModule
    let _ : IsScalarTower k K K :=
      IsScalarTower.of_algebraMap_eq (fun a => (e.commutes a).symm)
    let _ : FiniteDimensional K K :=
      RingHom.Finite.of_surjective e.toRingHom e.surjective
    ∀ w : Place k K, w.restrict K = (SemilinearAut.ofAlgAut e)⁻¹ • w := by
  intro aKK sKK mKK hkKK hKK w
  have he : e.toAlgHom.toRingHom.IsIntegral :=
    fun x => Algebra.IsIntegral.isIntegral (R := K) x
  exact Place.restrictAlong_eq_smul_of_forall_eq_inv_smul_pow
    1 one_ne_zero (SemilinearAut.ofAlgAut e)⁻¹ e.toAlgHom he
    (fun x => by simp only [inv_inv, pow_one]; rfl) w

section Covariance

variable {k : Type u} {K : Type v} {F : Type w}
    [Field k] [Finite k] [Field K] [Field F]
    [Algebra k K] [Algebra k F]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k F]

/-- A compatible original ambient isomorphism sends every lower Hilbert
element into the actual upper Hilbert image. The split-place condition is
the actual restriction of places for the given field isomorphism. -/
theorem hilbertClassField_image_map_of_algEquiv
    (eK : K ≃ₐ[k] F)
    (S : Finset (Place k K)) (hS : S.Nonempty)
    (T : Finset (Place k F)) (hT : T.Nonempty) :
    let _ : Algebra K F := eK.toRingHom.toAlgebra
    let _ : IsScalarTower k K F :=
      IsScalarTower.of_algebraMap_eq (fun a => (eK.commutes a).symm)
    let _ : FiniteDimensional K F :=
      RingHom.Finite.of_surjective eK.toRingHom eK.surjective
    ∀ (_ : ∀ w ∈ T, w.restrict K ∈ S)
      (Ω : Type x) [Field Ω] [Algebra K Ω] [Algebra F Ω]
      (i₀ : (hilbertClassField k K S hS).val →ₐ[K] Ω)
      (i₁ : (hilbertClassField k F T hT).val →ₐ[F] Ω)
      (σ : Ω ≃+* Ω)
      (_ : ∀ a : K, σ (algebraMap K Ω a) = algebraMap F Ω (eK a))
      (a : (hilbertClassField k K S hS).val),
      ∃ b : (hilbertClassField k F T hT).val, i₁ b = σ (i₀ a) := by
  intro aKF hkKF hKF hTS Ω hΩ aKΩ aFΩ i₀ i₁ σ hσ a
  let eK' : K ≃ₐ[K] F := { eK.toRingEquiv with commutes' := fun _ => rfl }
  have habelian : IsAbelianGalois K F :=
    IsAbelianGalois.of_algHom eK'.symm.toAlgHom
  let H₀ := hilbertClassField k K S hS
  let H₁ := hilbertClassField k F T hT
  let i₀ring : H₀.val →+* Ω := i₀.toRingHom
  have hi₀ (a : K) : i₀ring (algebraMap K H₀.val a) = algebraMap K Ω a :=
    i₀.commutes a
  let aKΩ' : Algebra K Ω := ((algebraMap F Ω).comp eK.toRingHom).toAlgebra
  have hKFΩ : IsScalarTower K F Ω :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let aKH₁ : Algebra K H₁.val :=
    ((algebraMap F H₁.val).comp eK.toRingHom).toAlgebra
  have hKFH₁ : IsScalarTower K F H₁.val :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let j₀ : H₀.val →ₐ[K] Ω :=
    { toRingHom := σ.toRingHom.comp i₀ring
      commutes' a := by
        change σ (i₀ring (algebraMap K H₀.val a)) = algebraMap F Ω (eK a)
        rw [hi₀, hσ] }
  have hi : j₀.fieldRange ≤ (i₁.restrictScalars K).fieldRange :=
    hilbertClassFieldImage_mono S hS T hT hTS Ω j₀ i₁
  exact hi ⟨a, rfl⟩

end Covariance

section Automorphism

variable {k : Type u} {K : Type v} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K]

/-- An original ambient automorphism preserving the chosen place actually
stabilizes its pointed Hilbert field. The output is its literal restriction,
with both the original coefficient identity and the base-field square. -/
theorem exists_hilbertClassFieldAutomorphism_of_fixed_place (v : Place k K) :
    let H := hilbertClassField k K {v} (Finset.singleton_nonempty _)
    let _ : Algebra k (SeparableClosure K) :=
      ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
    let _ : IsScalarTower k K (SeparableClosure K) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    ∀ (Ω : Type x) [Field Ω] [Algebra K Ω]
      (i : H.val →ₐ[K] Ω) (eK : K ≃ₐ[k] K) (σ : Ω ≃+* Ω)
      (_ : ∀ a : K, σ (algebraMap K Ω a) = algebraMap K Ω (eK a))
      (_ : SemilinearAut.ofAlgAut eK • v = v),
      ∃ eH : H.val ≃ₐ[k] H.val,
        (∀ a : H.val, i (eH a) = σ (i a)) ∧
        (∀ a : K, eH (algebraMap K H.val a) = algebraMap K H.val (eK a)) := by
  intro H akΩ hkKΩ Ω hΩ aKΩ i eK σ hσ hv
  have hinv : (SemilinearAut.ofAlgAut eK)⁻¹ • v = v := by
    rw [inv_smul_eq_iff, hv]
  have hsymm : (SemilinearAut.ofAlgAut eK.symm)⁻¹ • v = v := by
    change (SemilinearAut.ofAlgAut (eK⁻¹))⁻¹ • v = v
    rw [map_inv, inv_inv]
    exact hv
  have hσinv : ∀ a : K,
      σ.symm (algebraMap K Ω a) = algebraMap K Ω (eK.symm a) := by
    intro a
    apply σ.injective
    rw [σ.apply_symm_apply, hσ, eK.apply_symm_apply]
  have hforward : ∀ a : H.val, ∃ b : H.val, i b = σ (i a) := by
    refine hilbertClassField_image_map_of_algEquiv eK
      {v} (Finset.singleton_nonempty _) {v} (Finset.singleton_nonempty _)
      ?_ Ω i i σ hσ
    intro w hw
    have hwv : w = v := Finset.mem_singleton.mp hw
    subst w
    exact Finset.mem_singleton.mpr ((restrict_algAut eK v).trans hinv)
  have hbackward : ∀ a : H.val, ∃ b : H.val, i b = σ.symm (i a) := by
    refine hilbertClassField_image_map_of_algEquiv eK.symm
      {v} (Finset.singleton_nonempty _) {v} (Finset.singleton_nonempty _)
      ?_ Ω i i σ.symm hσinv
    intro w hw
    have hwv : w = v := Finset.mem_singleton.mp hw
    subst w
    exact Finset.mem_singleton.mpr ((restrict_algAut eK.symm v).trans hsymm)
  let f : H.val → H.val := fun a => Classical.choose (hforward a)
  let b : H.val → H.val := fun a => Classical.choose (hbackward a)
  have hf (a : H.val) : i (f a) = σ (i a) := Classical.choose_spec (hforward a)
  have hb (a : H.val) : i (b a) = σ.symm (i a) := Classical.choose_spec (hbackward a)
  let eH : H.val ≃ₐ[k] H.val :=
    { toFun := f
      invFun := b
      left_inv a := i.injective (by
        change i (b (f a)) = i a
        rw [hb, hf, σ.symm_apply_apply])
      right_inv a := i.injective (by
        change i (f (b a)) = i a
        rw [hf, hb, σ.apply_symm_apply])
      map_mul' a b := by
        apply i.injective
        change i (f (a * b)) = i (f a * f b)
        simp only [hf, map_mul]
      map_add' a b := by
        apply i.injective
        change i (f (a + b)) = i (f a + f b)
        simp only [hf, map_add]
      commutes' a := by
        apply i.injective
        change i (f (algebraMap k H.val a)) = i (algebraMap k H.val a)
        rw [hf, IsScalarTower.algebraMap_apply k K H.val, i.commutes, hσ, eK.commutes] }
  refine ⟨eH, hf, ?_⟩
  intro a
  apply i.injective
  change i (f (algebraMap K H.val a)) = i (algebraMap K H.val (eK a))
  rw [hf, i.commutes, hσ, i.commutes]

end Automorphism

end FunctionField

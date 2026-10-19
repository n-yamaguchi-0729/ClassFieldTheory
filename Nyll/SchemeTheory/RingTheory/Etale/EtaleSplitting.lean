/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgHom_nonempty_equiv_fin_of_tensorProduct_algEquiv_pi.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.Tactic.Push
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Alg Hom nonempty equiv fin of tensor Product alg Equiv pi
-/

section AlgHom_nonempty_equiv_fin_of_tensorProduct_algEquiv_pi

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace AlgHom_nonempty_equiv_fin_of_tensorProduct_algEquiv_pi

universe u v w w'

open TensorProduct

namespace AlgHom

export _root_.AlgHom (ext commutes restrictScalars comp toRingHom)

namespace CountSplit

open _root_.AlgHom


theorem exists_eq_evalAlgHom {Ω : Type*} [Field Ω] {d : ℕ} (F : (Fin d → Ω) →ₐ[Ω] Ω) :
    ∃ j : Fin d, F = Pi.evalAlgHom Ω (fun _ => Ω) j := by
  classical
  have hidem : ∀ j, F (Pi.single j 1) = 0 ∨ F (Pi.single j 1) = 1 := fun j => by
    have h : F (Pi.single j 1) * F (Pi.single j 1) = F (Pi.single j 1) := by
      rw [← map_mul]; congr 1; ext k; by_cases hk : k = j <;> simp [hk]
    rcases mul_eq_zero.mp
      (by rw [mul_sub, mul_one, h, sub_self] : F (Pi.single j 1) * (F (Pi.single j 1) - 1) = 0)
      with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  have hone : (∑ j, (Pi.single j (1 : Ω) : Fin d → Ω)) = 1 := by
    ext l; simp [Finset.sum_apply, Pi.single_apply]
  have hsum : ∑ j, F (Pi.single j 1) = 1 := by
    rw [← map_sum, hone, map_one]
  obtain ⟨j, hj⟩ : ∃ j, F (Pi.single j 1) = 1 := by
    by_contra h
    push Not at h
    have : ∑ j, F (Pi.single j (1 : Ω)) = 0 := Finset.sum_eq_zero fun j _ => (hidem
      j).resolve_right (h j)
    rw [this] at hsum
    exact zero_ne_one hsum
  refine ⟨j, ?_⟩
  ext x
  have horth : ∀ k, k ≠ j → F (Pi.single k 1) = 0 := fun k hk => by
    have h0 : (Pi.single k (1 : Ω) : Fin d → Ω) * Pi.single j 1 = 0 := by
      ext l; by_cases hl : l = k <;> by_cases hl' : l = j <;> simp_all
    have := congrArg F h0
    rw [map_mul, hj, mul_one, map_zero] at this
    exact this
  have hx : x = ∑ k, x k • (Pi.single k (1 : Ω) : Fin d → Ω) := by
    ext l; simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
  rw [Pi.evalAlgHom_apply, hx, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j (fun k _ hk =>
    by rw [horth k hk, mul_zero]) (fun h => absurd (Finset.mem_univ j) h),
    Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (fun h => absurd (Finset.mem_univ j) h)]
  simp [hj]

/-- Identify an algebra homomorphism from a finite product of fields with its evaluation index. -/
noncomputable def equivFinOfPi (Ω : Type*) [Field Ω] (d : ℕ) : ((Fin d → Ω) →ₐ[Ω] Ω) ≃ Fin d := by
  classical
  refine Equiv.ofBijective (fun F => (exists_eq_evalAlgHom F).choose) ⟨?_, ?_⟩
  · intro F G h
    rw [(exists_eq_evalAlgHom F).choose_spec, (exists_eq_evalAlgHom G).choose_spec]
    exact congrArg _ h
  · intro j
    refine ⟨Pi.evalAlgHom Ω (fun _ => Ω) j, ?_⟩
    have h := (exists_eq_evalAlgHom (Pi.evalAlgHom Ω (fun _ : Fin d => Ω) j)).choose_spec
    by_contra hne
    have := congrArg (fun F : (Fin d → Ω) →ₐ[Ω] Ω => F (Pi.single j 1)) h
    simp only [Pi.evalAlgHom_apply, Pi.single_eq_same] at this
    have hne' : (exists_eq_evalAlgHom (Pi.evalAlgHom Ω (fun _ : Fin d => Ω) j)).choose ≠ j := hne
    rw [Pi.single_apply, ite_eq_right hne'] at this
    exact one_ne_zero this

/-- The scalar-extension equivalence between algebra homomorphisms to `Ω`. -/
noncomputable def equivTensor (A : Type u) [CommRing A] (B : Type w) [CommRing B] [Algebra A B]
    (Ω : Type w') [Field Ω] [Algebra A Ω] : (B →ₐ[A] Ω) ≃ (Ω ⊗[A] B →ₐ[Ω] Ω) where
  toFun ψ := Algebra.TensorProduct.lift (AlgHom.id Ω Ω) ψ (fun _ _ => Commute.all _ _)
  invFun F := (F.restrictScalars A).comp Algebra.TensorProduct.includeRight
  left_inv ψ := by
    apply AlgHom.ext
    intro b
    change Algebra.TensorProduct.lift (AlgHom.id Ω Ω) ψ (fun _ _ => Commute.all _ _)
      ((1 : Ω) ⊗ₜ[A] b) = ψ b
    rw [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, one_mul]
  right_inv F := by
    apply Algebra.TensorProduct.ext'
    intro x b
    have hx : x ⊗ₜ[A] b = x • ((1 : Ω) ⊗ₜ[A] b) :=
      by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [Algebra.TensorProduct.lift_tmul]
    change x * F ((1 : Ω) ⊗ₜ[A] b) = F (x ⊗ₜ[A] b)
    rw [hx, map_smul, smul_eq_mul]

/-- The product decomposition after base change along the homomorphism to `Ω`. -/
noncomputable def tensorEquivPi {A : Type u} [CommRing A] {R' : Type v} [CommRing R'] [Algebra A R']
    {B : Type w} [CommRing B] [Algebra A B] {d : ℕ} (φ : R' ⊗[A] B ≃ₐ[R'] (Fin d → R'))
    {Ω : Type w'} [Field Ω] [Algebra A Ω] (t₀ : R' →ₐ[A] Ω) :
    Ω ⊗[A] B ≃ₐ[Ω] (Fin d → Ω) := by
  letI : Algebra R' Ω := t₀.toRingHom.toAlgebra
  haveI : IsScalarTower A R' Ω := IsScalarTower.of_algebraMap_eq fun a => (t₀.commutes a).symm
  exact (Algebra.TensorProduct.cancelBaseChange A R' Ω Ω B).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : Ω ≃ₐ[Ω] Ω) φ).trans
      ((Algebra.TensorProduct.piRight R' Ω Ω (fun _ : Fin d => R')).trans
        (AlgEquiv.piCongrRight fun _ => Algebra.TensorProduct.rid R' Ω Ω)))

end AlgHom.CountSplit

open AlgHom.CountSplit in
theorem _root_.AlgHom.nonempty_equiv_fin_of_tensorProduct_algEquiv_pi
    {A : Type u} [CommRing A] {R' : Type v} [CommRing R'] [Algebra A R']
    {B : Type w} [CommRing B] [Algebra A B] {d : ℕ}
    (φ : R' ⊗[A] B ≃ₐ[R'] (Fin d → R'))
    {Ω : Type w'} [Field Ω] [Algebra A Ω] (t₀ : R' →ₐ[A] Ω) :
    Nonempty ((B →ₐ[A] Ω) ≃ Fin d) :=
  ⟨(equivTensor A B Ω).trans (((tensorEquivPi φ t₀).arrowCongr AlgEquiv.refl).trans (equivFinOfPi Ω
    d))⟩
end AlgHom_nonempty_equiv_fin_of_tensorProduct_algEquiv_pi
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation

end AlgHom_nonempty_equiv_fin_of_tensorProduct_algEquiv_pi

section Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq

/-!
# Finite étale splitting with prescribed rank

Use the finite split algebra supplied by Mathlib and recover the prescribed number of factors
from its rank at a prime of the covering algebra.
-/

open scoped TensorProduct

namespace Algebra.Etale

universe u

theorem exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq
    (R : Type u) [CommRing R] (B : Type u) [CommRing B] [Algebra R B]
    [Module.Finite R B] [Algebra.Etale R B]
    (n : ℕ) (hn : ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) B p = n) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Module.Finite R R')
      (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R'),
      Nonempty ((R' ⊗[R] B) ≃ₐ[R'] (Fin n → R')) := by
  obtain ⟨T, hT, hRT, hflat, hfinite, hetale, hsplit⟩ :=
    Algebra.IsFiniteSplit.exists_tensorProduct_of_etale (R := R) (S := B) (funext hn)
  refine ⟨T, hT, hRT, hfinite, hetale, hflat, ?_⟩
  cases subsingleton_or_nontrivial T with
  | inl htrivial => exact ⟨default⟩
  | inr hnontrivial =>
    obtain ⟨m, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun T (T ⊗[R] B)
    obtain ⟨p⟩ := (PrimeSpectrum.nonempty_iff_nontrivial (R := T)).mpr hnontrivial
    have hm : Module.rankAtStalk (R := T) (Fin m → T) p = m := by
      rw [Module.rankAtStalk_pi]
      simp only [Module.rankAtStalk_self, Pi.one_apply, finsum_eq_sum_of_fintype,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, mul_one]
    have hmn : m = n := calc
      m = Module.rankAtStalk (R := T) (Fin m → T) p := hm.symm
      _ = Module.rankAtStalk (R := T) (T ⊗[R] B) p :=
        congrFun (Module.rankAtStalk_eq_of_equiv e.symm.toLinearEquiv) p
      _ = Module.rankAtStalk (R := R) B (p.comap (algebraMap R T)) :=
        Module.rankAtStalk_baseChange p
      _ = n := hn _
    subst m
    exact ⟨e⟩

end Algebra.Etale

end Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq

section Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi

/-!
# Algebra Etale exists finite etale faithfully Flat tensor Product alg Equiv pi
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi

open scoped TensorProduct

universe u

theorem _root_.Algebra.Etale.exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B] [Algebra.Etale R B] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Module.Finite R R')
      (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R') (_ : IsNoetherianRing R'),
      Nonempty ((R' ⊗[R] B) ≃ₐ[R'] (Fin (Module.finrank R B) → R')) := by
  let _ : Module.Free R B := Module.free_of_flat_of_isLocalRing
  obtain ⟨R', _, _, _, _, _, ⟨e⟩⟩ :=
    Algebra.Etale.exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi_of_rankAtStalk_eq R B
      (Module.finrank R B) (fun p => by rw [Module.rankAtStalk_eq_finrank_of_free]; rfl)
  exact ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Algebra.FiniteType.isNoetherianRing R R', ⟨e⟩⟩
end Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation

end Algebra_Etale_exists_finite_etale_faithfullyFlat_tensorProduct_algEquiv_pi

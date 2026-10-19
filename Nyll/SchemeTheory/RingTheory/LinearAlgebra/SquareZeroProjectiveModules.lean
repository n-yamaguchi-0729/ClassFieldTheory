/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_Projective_exists_baseChange_quotient_iso_of_squareZero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_Projective_exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_Projective_nonempty_linearEquiv_of_baseChange_quotient_of_squareZero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_finrank_baseChange_eq_of_quotient_squareZero_linearEquiv.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Ring.RingNF
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
Lifting projective modules across a square-zero quotient using base change.
-/

section Module_Projective_exists_baseChange_quotient_iso_of_squareZero

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Module_Projective_exists_baseChange_quotient_iso_of_squareZero

universe u

open TensorProduct Polynomial

theorem _root_.Module.Projective.exists_baseChange_quotient_iso_of_squareZero
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    (P : Type u) [AddCommGroup P] [Module (R ⧸ I) P]
    [Module.Projective (R ⧸ I) P] [Module.Finite (R ⧸ I) P] :
    ∃ (P' : Type u) (_ : AddCommGroup P') (_ : Module R P'),
      Module.Projective R P' ∧ Module.Finite R P' ∧
      Nonempty (((R ⧸ I) ⊗[R] P') ≃ₗ[R ⧸ I] P) := by
  classical
  let : Module R P := Module.compHom P (algebraMap R (R ⧸ I))
  have hPsmul : ∀ (r : R) (p : P), r • p = (Ideal.Quotient.mk I r) • p := fun r p => by
    change (algebraMap R (R⧸I) r) • p = _; rw [Ideal.Quotient.algebraMap_eq]
  let : IsScalarTower R (R ⧸ I) P :=
    ⟨fun r c p => by
      rw [hPsmul, ← smul_assoc, smul_eq_mul, ← Ideal.Quotient.algebraMap_eq, ← Algebra.smul_def]⟩
  have hII : ∀ a ∈ I, ∀ b ∈ I, a * b = 0 := fun a ha b hb => by
    have h := Ideal.mul_mem_mul ha hb; rwa [← pow_two, hI, Ideal.mem_bot] at h
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (R ⧸ I) P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hfs : ∀ p, f (s p) = p := fun p => LinearMap.congr_fun hs p
  let e : Module.End (R⧸I) (Fin n → R⧸I) := s ∘ₗ f
  have he_idem : e * e = e := LinearMap.ext fun v => by
    change s (f (s (f v))) = s (f v); rw [hfs]
  have hesp : ∀ p, e (s p) = s p := fun p => by
    change s (f (s p)) = s p; rw [hfs]
  let q : (Fin n → R) →ₗ[R] (Fin n → R⧸I) :=
    LinearMap.pi fun i => (Algebra.linearMap R (R⧸I)).comp (LinearMap.proj i)
  have hq_apply : ∀ (v : Fin n → R) i, q v i = Ideal.Quotient.mk I (v i) := fun v i => by
    simp only [q, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Algebra.linearMap_apply, Ideal.Quotient.algebraMap_eq]
  have hq_surj : Function.Surjective q := fun w => by
    choose g hg using fun i => Ideal.Quotient.mk_surjective (w i)
    exact ⟨g, funext fun i => (hq_apply g i).trans (hg i)⟩
  have hq_ker : ∀ v, q v = 0 ↔ ∀ i, v i ∈ I := fun v => by
    simp only [funext_iff, hq_apply, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨e', he'⟩ :=
    Module.projective_lifting_property q ((e.restrictScalars R).comp q) hq_surj
  have he'_reduce : ∀ v, q (e' v) = e (q v) := fun v => LinearMap.congr_fun he' v
  let η : Module.End R (Fin n → R) := e' * e' - e'
  have hη_ker : ∀ v, q (η v) = 0 := fun v => by
    have : q (e' (e' v)) - q (e' v) = 0 := by
      rw [he'_reduce, he'_reduce, ← Module.End.mul_apply, he_idem, sub_self]
    simpa only [η, Module.End.mul_apply, LinearMap.sub_apply, map_sub] using this
  have hη_I : ∀ v i, η v i ∈ I := fun v i => (hq_ker _).mp (hη_ker v) i
  have hbasis : ∀ (w : Fin n → R), w = ∑ j, (w j) • Pi.single j (1 : R) := fun w => by
    ext k; simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  have hηη : η * η = 0 := LinearMap.ext fun v => funext fun i => by
    simp only [Module.End.mul_apply, LinearMap.zero_apply, Pi.zero_apply]
    conv_lhs => rw [hbasis (η v), map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_eq_zero fun j _ => hII (η v j) (hη_I v j) _ (hη_I _ i)
  let e'' : Module.End R (Fin n → R) := 3 • (e' * e') - 2 • (e' * e' * e')
  have he''_reduce : ∀ v, q (e'' v) = e (q v) := fun v => by
    have h1 : q (e' (e' v)) = e (q v) := by
      rw [he'_reduce, he'_reduce, ← Module.End.mul_apply, he_idem]
    have h2 : q (e' (e' (e' v))) = e (q v) := by
      rw [he'_reduce, he'_reduce, he'_reduce, ← Module.End.mul_apply,
        ← Module.End.mul_apply, he_idem, he_idem]
    simp only [e'', LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
      map_sub, map_nsmul, h1, h2]
    abel
  have he''_idem : e'' * e'' = e'' := by
    have hφe'' : aeval (R := R) e' (3 * X^2 - 2 * X^3 : R[X]) = e'' := by
      rw [map_sub, map_mul, map_mul, map_pow, map_pow, aeval_X, map_ofNat, map_ofNat,
        show (3 : Module.End R (Fin n → R)) = ((3:ℕ) : Module.End R (Fin n → R)) from by norm_cast,
        show (2 : Module.End R (Fin n → R)) = ((2:ℕ) : Module.End R (Fin n → R)) from by norm_cast,
        ← nsmul_eq_mul, ← nsmul_eq_mul, sq, pow_succ, sq]
    have hφη : aeval (R := R) e' (X^2 - X : R[X]) = η := by
      rw [map_sub, map_pow, aeval_X, sq]
    have hpoly : ((3*X^2 - 2*X^3 : R[X])^2 - (3*X^2 - 2*X^3))
        = (X^2 - X)^2 * (4*X^2 - 4*X - 3) := by ring
    have key := congrArg (aeval (R := R) e') hpoly
    rw [map_sub, map_pow, map_mul, map_pow, hφe'', hφη,
      show e''^2 = e''*e'' from sq e'',
      show η^2 = η*η from sq η, hηη, zero_mul, sub_eq_zero] at key
    exact key
  have he''_fix : ∀ v ∈ LinearMap.range e'', e'' v = v := fun v ⟨y, hy⟩ => by
    rw [← hy, ← Module.End.mul_apply, he''_idem]
  refine ⟨LinearMap.range e'', inferInstance, inferInstance, ?_, ?_, ?_⟩
  · refine Module.Projective.of_split (LinearMap.range e'').subtype e''.rangeRestrict ?_
    exact LinearMap.ext fun p' => Subtype.ext (he''_fix p'.val p'.property)
  · exact Module.Finite.range e''
  · set P' : Submodule R (Fin n → R) := LinearMap.range e''
    let α : P' →ₗ[R] P := (f.restrictScalars R) ∘ₗ q ∘ₗ P'.subtype
    have hα_app : ∀ p' : P', α p' = f (q p'.val) := fun _ => rfl
    have hα_surj : Function.Surjective α := fun p => by
      obtain ⟨v, hv⟩ := hq_surj (s p)
      exact ⟨⟨e'' v, LinearMap.mem_range_self _ _⟩, by
        rw [hα_app, he''_reduce, hv, hesp, hfs]⟩
    have hα_ker : LinearMap.ker α = I • (⊤ : Submodule R P') := by
      ext p'
      simp only [LinearMap.mem_ker, hα_app]
      constructor
      · intro hp'
        have hqr : q p'.val ∈ LinearMap.range e := by
          obtain ⟨y, hy⟩ := p'.property; exact ⟨q y, by rw [← hy, he''_reduce]⟩
        obtain ⟨w, hw⟩ := hqr
        have hfw : f w = 0 := by
          have : f (s (f w)) = 0 := by change f (e w) = 0; rw [hw]; exact hp'
          rwa [hfs] at this
        have hq0 : q p'.val = 0 := by rw [← hw]; change s (f w) = 0; rw [hfw, map_zero]
        have hcoord : ∀ i, p'.val i ∈ I := (hq_ker _).mp hq0
        rw [Submodule.mem_smul_top_iff]
        change (p' : Fin n → R) ∈ I • P'
        rw [← he''_fix p'.val p'.property, hbasis p'.val, map_sum]
        simp only [map_smul]
        exact Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem_smul (hcoord i) (LinearMap.mem_range_self _ _)
      · intro hp'
        refine Submodule.smul_induction_on hp' (fun a ha w _ => ?_)
          (fun x y hx hy => by
            change f (q ((x : Fin n → R) + (y : Fin n → R))) = 0
            rw [map_add, map_add, hx, hy, add_zero])
        change f (q (a • (↑w : Fin n → R))) = 0
        have hq0 : q (a • (↑w : Fin n → R)) = 0 := funext fun i => by
          simp only [hq_apply, Pi.smul_apply, smul_eq_mul, map_mul, Pi.zero_apply]
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul]
        rw [hq0, map_zero]
    let ψ₁ : (R ⧸ I) ⊗[R] P' ≃ₗ[R] P' ⧸ (I • (⊤:Submodule R P')) := quotTensorEquivQuotSMul P' I
    let ψ₂ : (P' ⧸ (I • (⊤:Submodule R P'))) ≃ₗ[R] P :=
      (Submodule.quotEquivOfEq _ _ hα_ker.symm).trans
        (LinearMap.quotKerEquivOfSurjective α hα_surj)
    let ψ : (R ⧸ I) ⊗[R] P' ≃ₗ[R] P := ψ₁.trans ψ₂
    refine ⟨⟨⟨⟨ψ, ψ.map_add⟩, ?_⟩, ψ.symm, ψ.left_inv, ψ.right_inv⟩⟩
    intro c z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    simp only [RingHom.id_apply]
    rw [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul, ψ.map_smul,
      ← IsScalarTower.algebraMap_smul (R⧸I) r (ψ z)]
end Module_Projective_exists_baseChange_quotient_iso_of_squareZero
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation

end Module_Projective_exists_baseChange_quotient_iso_of_squareZero

section Module_Projective_exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat

/-!
Lift compatible projective-module identifications across a square-zero quotient.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Module_Projective_exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat

universe u

open TensorProduct

open scoped _root_.Module _root_.Module.Projective in
private lemma le_jacobson_bot_of_sq_eq_bot_aux
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥) :
    I ≤ (⊥ : Ideal R).jacobson := by
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  have hxx : x * x = 0 := by
    have hmem : x * x ∈ I ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul hx hx
    rw [hI] at hmem
    simpa using hmem
  have hxy : IsNilpotent (x * y) := ⟨2, by
    calc (x * y) ^ 2 = (x * x) * (y * y) := by ring
      _ = 0 := by rw [hxx, zero_mul]⟩
  exact hxy.isUnit_add_one

open scoped _root_.Module _root_.Module.Projective in
private lemma surjective_of_one_tmul_aux
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson)
    {N M : Type u} [AddCommGroup N] [AddCommGroup M] [Module R N] [Module R M]
    [Module.Finite R M] (f : N →ₗ[R] M)
    (hf : ∀ m : M, ∃ n : N, (1 : R ⧸ I) ⊗ₜ[R] f n = (1 : R ⧸ I) ⊗ₜ[R] m) :
    Function.Surjective f := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI ?_
  intro m _
  obtain ⟨n, hn⟩ := hf m
  have key : ∀ x : M, quotTensorEquivQuotSMul M I ((1 : R ⧸ I) ⊗ₜ[R] x) =
      Submodule.Quotient.mk x := by
    intro x
    rw [← map_one (Ideal.Quotient.mk I), quotTensorEquivQuotSMul_mk_tmul, one_smul]
  have hq : (Submodule.Quotient.mk (f n) : M ⧸ (I • ⊤ : Submodule R M)) =
      Submodule.Quotient.mk m := by
    rw [← key, ← key, hn]
  have hmem : f n - m ∈ I • (⊤ : Submodule R M) := (Submodule.Quotient.eq _).mp hq
  have hsplit : m = f n - (f n - m) := by abel
  rw [hsplit]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left (LinearMap.mem_range_self f n))
    (Submodule.mem_sup_right hmem)

theorem _root_.Module.Projective.exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    (P₁ P₂ : Type u) [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₁] [Module R P₂]
    [Module.Projective R P₁] [Module.Finite R P₁]
    [Module.Projective R P₂] [Module.Finite R P₂]
    (e : ((R ⧸ I) ⊗[R] P₁) ≃ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] P₂)) :
    ∃ σ' : P₁ ≃ₗ[R] P₂, ∀ p : P₁, (1 : R ⧸ I) ⊗ₜ[R] σ' p = e ((1 : R ⧸ I) ⊗ₜ[R] p) := by
  have hmk₁ : Function.Surjective (TensorProduct.mk R (R ⧸ I) P₁ 1) :=
    TensorProduct.mk_surjective R P₁ (R ⧸ I) Ideal.Quotient.mk_surjective
  have hmk₂ : Function.Surjective (TensorProduct.mk R (R ⧸ I) P₂ 1) :=
    TensorProduct.mk_surjective R P₂ (R ⧸ I) Ideal.Quotient.mk_surjective
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (TensorProduct.mk R (R ⧸ I) P₂ 1)
    ((e.restrictScalars R).toLinearMap ∘ₗ TensorProduct.mk R (R ⧸ I) P₁ 1) hmk₂
  obtain ⟨g, hg⟩ := Module.projective_lifting_property (TensorProduct.mk R (R ⧸ I) P₁ 1)
    ((e.symm.restrictScalars R).toLinearMap ∘ₗ TensorProduct.mk R (R ⧸ I) P₂ 1) hmk₁
  have hf' : ∀ p : P₁, (1 : R ⧸ I) ⊗ₜ[R] f p = e ((1 : R ⧸ I) ⊗ₜ[R] p) := fun p =>
    LinearMap.congr_fun hf p
  have hg' : ∀ q : P₂, (1 : R ⧸ I) ⊗ₜ[R] g q = e.symm ((1 : R ⧸ I) ⊗ₜ[R] q) := fun q =>
    LinearMap.congr_fun hg q
  have hgf : ∀ p : P₁, (1 : R ⧸ I) ⊗ₜ[R] (g ∘ₗ f) p = (1 : R ⧸ I) ⊗ₜ[R] p := fun p => by
    rw [LinearMap.comp_apply, hg', hf', LinearEquiv.symm_apply_apply]
  have hfg : ∀ q : P₂, (1 : R ⧸ I) ⊗ₜ[R] (f ∘ₗ g) q = (1 : R ⧸ I) ⊗ₜ[R] q := fun q => by
    rw [LinearMap.comp_apply, hf', hg', LinearEquiv.apply_symm_apply]
  have hJ := le_jacobson_bot_of_sq_eq_bot_aux I hI
  have sgf : Function.Surjective (g ∘ₗ f) :=
    surjective_of_one_tmul_aux I hJ (g ∘ₗ f) fun p => ⟨p, hgf p⟩
  have sfg : Function.Surjective (f ∘ₗ g) :=
    surjective_of_one_tmul_aux I hJ (f ∘ₗ g) fun q => ⟨q, hfg q⟩
  have igf : Function.Injective (g ∘ₗ f) :=
    OrzechProperty.injective_of_surjective_endomorphism _ sgf
  rw [LinearMap.coe_comp] at igf sfg
  have hbij : Function.Bijective f := ⟨igf.of_comp, sfg.of_comp⟩
  exact ⟨LinearEquiv.ofBijective f hbij, fun p => hf' p⟩
end Module_Projective_exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation

end Module_Projective_exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat

section Module_Projective_nonempty_linearEquiv_of_baseChange_quotient_of_squareZero

/-!
Compare projective modules after base change across a square-zero quotient.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Module_Projective_nonempty_linearEquiv_of_baseChange_quotient_of_squareZero

universe u

open TensorProduct

theorem _root_.Module.Projective.nonempty_linearEquiv_of_baseChange_quotient_of_squareZero
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    (P₁ P₂ : Type u) [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₁] [Module R P₂]
    [Module.Projective R P₁] [Module.Finite R P₁]
    [Module.Projective R P₂] [Module.Finite R P₂]
    (e : ((R ⧸ I) ⊗[R] P₁) ≃ₗ[R ⧸ I] ((R ⧸ I) ⊗[R] P₂)) :
    Nonempty (P₁ ≃ₗ[R] P₂) := by
  classical
  have hIjac : I ≤ (⊥ : Ideal R).jacobson := by
    rw [Ideal.jacobson_bot]
    refine le_trans (fun a ha => ?_) (nilradical_le_jacobson R)
    refine ⟨2, ?_⟩
    have hpow := Ideal.pow_mem_pow ha 2
    rw [hI] at hpow
    exact Ideal.mem_bot.mp hpow
  have hB : ∀ {P : Type u} [AddCommGroup P] [Module R P] (p : P),
      (1 : R⧸I) ⊗ₜ[R] p = 0 → p ∈ I • (⊤ : Submodule R P) := by
    intro P _ _ p hp
    rw [← Submodule.Quotient.mk_eq_zero]
    have h1 : (quotTensorEquivQuotSMul P I) ((1 : R⧸I) ⊗ₜ[R] p) = Submodule.Quotient.mk p :=
      quotTensorEquivQuotSMul_mk_one_tmul I p
    rw [← h1, hp, map_zero]
  let q₁ : P₁ →ₗ[R] (R ⧸ I) ⊗[R] P₁ := (TensorProduct.mk R (R ⧸ I) P₁) 1
  let q₂ : P₂ →ₗ[R] (R ⧸ I) ⊗[R] P₂ := (TensorProduct.mk R (R ⧸ I) P₂) 1
  have hqsurj : ∀ {P : Type u} [AddCommGroup P] [Module R P],
      Function.Surjective ((TensorProduct.mk R (R ⧸ I) P) 1) := by
    intro P _ _ z
    induction z using TensorProduct.inductionOn with
    | tmul r p =>
      obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective r
      refine ⟨r' • p, ?_⟩
      simp only [TensorProduct.mk_apply]
      rw [← Ideal.Quotient.algebraMap_eq, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨px, hpx⟩ := hx; obtain ⟨py, hpy⟩ := hy
      exact ⟨px + py, by simp only [map_add, hpx, hpy]⟩
  obtain ⟨f, hf⟩ :=
    Module.projective_lifting_property q₂ ((e.toLinearMap.restrictScalars R).comp q₁) hqsurj
  obtain ⟨f', hf'⟩ :=
    Module.projective_lifting_property q₁ ((e.symm.toLinearMap.restrictScalars R).comp q₂) hqsurj
  have hff' : ∀ p, q₁ (f' (f p)) = q₁ p := fun p => by
    have h1 : q₂ (f p) = e (q₁ p) := by
      exact congrFun (congrArg DFunLike.coe hf) p
    have h2 : q₁ (f' (f p)) = e.symm (q₂ (f p)) := by
      exact congrFun (congrArg DFunLike.coe hf') (f p)
    rw [h2, h1, LinearEquiv.symm_apply_apply]
  have hf'f : ∀ p, q₂ (f (f' p)) = q₂ p := fun p => by
    have h1 : q₁ (f' p) = e.symm (q₂ p) := by
      exact congrFun (congrArg DFunLike.coe hf') p
    have h2 : q₂ (f (f' p)) = e (q₁ (f' p)) := by
      exact congrFun (congrArg DFunLike.coe hf) (f' p)
    rw [h2, h1, LinearEquiv.apply_symm_apply]
  have hA : ∀ {P : Type u} [AddCommGroup P] [Module R P] [Module.Finite R P]
      (N : Submodule R P), N ⊔ I • ⊤ = ⊤ → N = ⊤ := by
    intro P _ _ _ N h
    refine le_antisymm le_top ?_
    exact Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hIjac
      (le_of_eq h.symm)
  have hff'_surj : Function.Surjective (f'.comp f) := by
    rw [← LinearMap.range_eq_top]
    refine hA _ ?_
    rw [eq_top_iff]; intro p _
    have hmem : p - f' (f p) ∈ I • (⊤ : Submodule R P₁) := by
      refine hB _ ?_
      have : q₁ (p - f' (f p)) = 0 := by rw [map_sub, hff' p, sub_self]
      simpa only [q₁, TensorProduct.mk_apply] using this
    exact Submodule.mem_sup.mpr ⟨f' (f p), LinearMap.mem_range.mpr ⟨p, rfl⟩,
      p - f' (f p), hmem, by abel⟩
  have hf'f_surj : Function.Surjective (f.comp f') := by
    rw [← LinearMap.range_eq_top]
    refine hA _ ?_
    rw [eq_top_iff]; intro p _
    have hmem : p - f (f' p) ∈ I • (⊤ : Submodule R P₂) := by
      refine hB _ ?_
      have : q₂ (p - f (f' p)) = 0 := by rw [map_sub, hf'f p, sub_self]
      simpa only [q₂, TensorProduct.mk_apply] using this
    exact Submodule.mem_sup.mpr ⟨f (f' p), LinearMap.mem_range.mpr ⟨p, rfl⟩,
      p - f (f' p), hmem, by abel⟩
  have hf_bij : Function.Bijective f :=
    ⟨fun a b hab =>
      (OrzechProperty.injective_of_surjective_endomorphism (f'.comp f) hff'_surj)
        (by simp only [LinearMap.comp_apply, hab]),
     fun p => let ⟨q, hq⟩ := hf'f_surj p; ⟨f' q, hq⟩⟩
  exact ⟨LinearEquiv.ofBijective f hf_bij⟩
end Module_Projective_nonempty_linearEquiv_of_baseChange_quotient_of_squareZero
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation

end Module_Projective_nonempty_linearEquiv_of_baseChange_quotient_of_squareZero

section Module_finrank_baseChange_eq_of_quotient_squareZero_linearEquiv

/-!
Preserve module rank under a square-zero quotient identification.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Module_finrank_baseChange_eq_of_quotient_squareZero_linearEquiv

universe u

open TensorProduct

theorem _root_.Module.finrank_baseChange_eq_of_quotient_squareZero_linearEquiv
    {R : Type u} [CommRing R] (J : Ideal R) (hJ : J ^ 2 = ⊥)
    {S : Type u} [CommRing S] (φ : R ⧸ J ≃+* S)
    (P : Type u) [AddCommGroup P] [Module S P]
    (P' : Type u) [AddCommGroup P'] [Module R P'] {n : ℕ}
    (hrk : ∀ (K : Type u) [Field K] [Algebra S K], Module.finrank K (K ⊗[S] P) = n) :
    letI : Module (R ⧸ J) P := Module.compHom P φ.toRingHom
    ((R ⧸ J) ⊗[R] P' ≃ₗ[R ⧸ J] P) →
    ∀ (K : Type u) [Field K] [Algebra R K], Module.finrank K (K ⊗[R] P') = n := by
  let : Module (R ⧸ J) P := Module.compHom P φ.toRingHom
  intro iso K _ _
  have hJK : ∀ x ∈ J, (algebraMap R K) x = 0 := fun x hx => by
    have h2 : (algebraMap R K x) ^ 2 = 0 := by
      rw [← map_pow]
      have : x ^ 2 = 0 := by
        have h := Ideal.pow_mem_pow hx 2; rw [hJ] at h; exact Ideal.mem_bot.mp h
      rw [this, map_zero]
    exact (pow_eq_zero_iff two_ne_zero).mp h2
  let : Algebra (R ⧸ J) K := (Ideal.Quotient.lift J (algebraMap R K) hJK).toAlgebra
  have : IsScalarTower R (R ⧸ J) K := IsScalarTower.of_algebraMap_eq'
    (RingHom.ext fun a => (Ideal.Quotient.lift_mk J (algebraMap R K) hJK).symm)
  have e1 : K ⊗[R] P' ≃ₗ[K] K ⊗[R ⧸ J] P :=
    (AlgebraTensorModule.cancelBaseChange R (R ⧸ J) K K P').symm.trans
      (LinearEquiv.baseChange (R ⧸ J) K ((R ⧸ J) ⊗[R] P') P iso)
  rw [e1.finrank_eq]
  let : Algebra S K := ((algebraMap (R ⧸ J) K).comp φ.symm.toRingHom).toAlgebra
  have keyeq : ∀ r : R ⧸ J, (algebraMap S K (φ r) : K) = algebraMap (R ⧸ J) K r := fun r => by
    change algebraMap (R ⧸ J) K (φ.symm (φ r)) = _; rw [φ.symm_apply_apply]
  let fwdAH : K ⊗[R ⧸ J] P →+ K ⊗[S] P := TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun k => AddMonoidHom.mk' (fun p => k ⊗ₜ[S] p)
        (fun _ _ => tmul_add k _ _))
      (fun _ _ => AddMonoidHom.ext fun _ => add_tmul _ _ _))
    (fun r k p => by
      change (algebraMap (R ⧸ J) K r * k) ⊗ₜ[S] p = k ⊗ₜ[S] ((φ r : S) • p)
      rw [← keyeq r]
      rw [show algebraMap S K (φ r) * k = (φ r : S) • k from (Algebra.smul_def (φ r) k).symm]
      exact smul_tmul (φ r) k p)
  let bwdAH : K ⊗[S] P →+ K ⊗[R ⧸ J] P := TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun k => AddMonoidHom.mk' (fun p => k ⊗ₜ[R ⧸ J] p)
        (fun _ _ => tmul_add k _ _))
      (fun _ _ => AddMonoidHom.ext fun _ => add_tmul _ _ _))
    (fun s k p => by
      change (algebraMap S K s * k) ⊗ₜ[R ⧸ J] p = k ⊗ₜ[R ⧸ J] (s • p)
      have hk : algebraMap S K s * k = (φ.symm s : R ⧸ J) • k := by
        rw [Algebra.smul_def]; rfl
      have hp : (s • p : P) = (φ.symm s : R ⧸ J) • p := by
        change s • p = (φ (φ.symm s) : S) • p; rw [φ.apply_symm_apply]
      rw [hk, hp]; exact smul_tmul (φ.symm s) k p)
  let e2AE : K ⊗[R ⧸ J] P ≃+ K ⊗[S] P :=
    { toFun := fwdAH
      invFun := bwdAH
      left_inv := fun x => by
        induction x using TensorProduct.inductionOn with
        | tmul k p => simp [fwdAH, bwdAH, liftAddHom_tmul]
        | add x y hx hy => simp only [map_add, hx, hy]
      right_inv := fun x => by
        induction x using TensorProduct.inductionOn with
        | tmul k p => simp [fwdAH, bwdAH, liftAddHom_tmul]
        | add x y hx hy => simp only [map_add, hx, hy]
      map_add' := map_add fwdAH }
  have e2 : K ⊗[R ⧸ J] P ≃ₗ[K] K ⊗[S] P := by
    refine AddEquiv.toLinearEquiv e2AE ?_
    intro c x
    induction x using TensorProduct.inductionOn with
    | tmul k p =>
        simp only [e2AE, fwdAH, AddEquiv.coe_mk, Equiv.coe_fn_mk, smul_tmul', liftAddHom_tmul,
          AddMonoidHom.mk'_apply]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  rw [e2.finrank_eq]
  exact hrk K
end Module_finrank_baseChange_eq_of_quotient_squareZero_linearEquiv
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation

end Module_finrank_baseChange_eq_of_quotient_squareZero_linearEquiv

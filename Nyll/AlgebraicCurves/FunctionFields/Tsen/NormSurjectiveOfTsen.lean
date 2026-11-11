/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Tsen
public import Nyll.SchemeTheory.RingTheory.Polynomial.NormPolynomial
public import Nyll.AlgebraicCurves.FunctionFields.Extensions.CurveFiniteExtension

/-!
# Surjectivity of finite-extension norms over curve function fields

The actual algebra norm is represented by a homogeneous form of degree equal to the extension
dimension. Tsen applied to N(Y) - a Z^d gives a nonzero point. Anisotropy of the field norm
forces Z to be nonzero, so division by Z gives norm a.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace AlgebraicCurve

/-- Every element of a one-variable function field over an algebraically closed field
is a norm from each of its finite field extensions. -/
theorem norm_surjective_of_transcendental_of_finiteDimensional
    (K : Type*) [Field K] [IsAlgClosed K] {F : Type*} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F)
    (E : Type*) [Field E] [Algebra F E] [FiniteDimensional F E] :
    Function.Surjective (Algebra.norm F : E →* F) := by
  classical
  intro a
  let r : ℕ := Module.finrank F E
  let b := Module.finBasis F E
  let Q : MvPolynomial (Fin (r + 1)) F :=
    MvPolynomial.rename Fin.castSucc b.normPolynomial -
      MvPolynomial.C a * MvPolynomial.X (Fin.last r) ^ r
  have hr : 0 < r := Module.finrank_pos
  have hb : b.normPolynomial.IsHomogeneous r := by
    simpa only [Fintype.card_fin] using b.normPolynomial_isHomogeneous
  have hQ : Q.IsHomogeneous r :=
    hb.rename_isHomogeneous.sub
      (MvPolynomial.isHomogeneous_C_mul_X_pow a (Fin.last r) r)
  obtain ⟨z, hz, hQz⟩ :=
    exists_ne_zero_homogeneous_zero_of_transcendental_of_finiteDimensional
      K x hx hfin hsep Q hQ hr (Nat.lt_succ_self r)
  let w : E := b.equivFun.symm (fun i => z i.castSucc)
  let t : F := z (Fin.last r)
  have hnw : Algebra.norm F w = a * t ^ r := by
    have h := hQz
    dsimp only [Q] at h
    rw [MvPolynomial.eval_sub, MvPolynomial.eval_rename,
      MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_pow,
      MvPolynomial.eval_X, Module.Basis.eval_normPolynomial] at h
    rw [← Module.Basis.equivFun_symm_apply] at h
    exact sub_eq_zero.mp h
  have ht : t ≠ 0 := by
    intro ht
    have hnw0 : Algebra.norm F w = 0 := by
      rw [hnw, ht, zero_pow (Nat.ne_of_gt hr), mul_zero]
    have hw : w = 0 := Algebra.norm_eq_zero_iff.mp hnw0
    apply hz
    funext i
    refine Fin.lastCases ht (fun j => ?_) i
    have hj := congrArg (fun v => b.equivFun v j) hw
    simpa only [w, LinearEquiv.apply_symm_apply, map_zero, Pi.zero_apply] using hj
  refine ⟨algebraMap F E t⁻¹ * w, ?_⟩
  rw [map_mul, Algebra.norm_algebraMap, hnw]
  change (t⁻¹) ^ r * (a * t ^ r) = a
  rw [inv_pow, mul_left_comm, inv_mul_cancel₀ (pow_ne_zero r ht), mul_one]

/-- Norm surjectivity is preserved after a finite extension of the curve function
field. The separating parameter is obtained from the existing perfect-field theorem. -/
theorem norm_surjective_over_finite_extension
    (K : Type*) [Field K] [IsAlgClosed K] {F : Type*} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (L : Type*) [Field L] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
    [FiniteDimensional F L]
    (E : Type*) [Field E] [Algebra L E] [FiniteDimensional L E] :
    Function.Surjective (Algebra.norm L : E →* L) := by
  obtain ⟨y, hy, hyfin, hysep⟩ :=
    exists_separating_transcendental_over_finite_extension K x hx hfin L
  exact norm_surjective_of_transcendental_of_finiteDimensional K y hy hyfin hysep E

end AlgebraicCurve

/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_norm_algebraMap_sub_eq_minpoly_eval.lean
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
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_norm_one_add_eps_tmul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_exists_monoidHom_algebraMap_eq_norm_of_isIntegrallyClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_norm_algebraMap_sub_eq_eval_minpoly_pow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_norm_algebraMap_eq_of_isPushout_of_isFractionRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_algebraMap_norm_eq_norm_mul_norm_of_adjoin_eq_top.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Tactic.Choose
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.Ring.RingNF

/-!
# Algebra norm of subsingleton
-/

@[expose] public section

section Algebra_norm_of_subsingleton

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_norm_of_subsingleton

theorem _root_.Algebra.norm_of_subsingleton {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  [Subsingleton A] (a : A) : Algebra.norm R a = 1 :=
  LinearMap.det_eq_one_of_subsingleton _
end AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_norm_of_subsingleton
end ProofImplementation

end Algebra_norm_of_subsingleton

section Algebra_norm_prod

/-!
# Algebra norm prod
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_norm_prod

theorem _root_.Algebra.norm_prod {R A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A]
  [Algebra R B] [Module.Free R A] [Module.Finite R A] [Module.Free R B] [Module.Finite R B] (x : A
  × B) : Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 := by
  have lmul_prod : Algebra.lmul R (A × B) x
      = ((Algebra.lmul R A x.1).prodMap (Algebra.lmul R B x.2) : A × B →ₗ[R] A × B) := by
    ext y <;> rfl
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, lmul_prod,
    LinearMap.det_prodMap]
end AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_norm_prod
end ProofImplementation

end Algebra_norm_prod

section Algebra_norm_algebraMap_sub_eq_minpoly_eval

/-!
# Algebra norm algebra Map sub eq minpoly eval
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_norm_algebraMap_sub_eq_minpoly_eval

open Polynomial IntermediateField

namespace S09NR

section Norm

variable {F F' : Type*} [Field F] [Field F'] [Algebra F F'] [Module.Finite F F']

theorem norm_algebraMap_sub (x : F') (hdeg : (minpoly F x).natDegree = Module.finrank F F') (c : F)
  :
    Algebra.norm F (algebraMap F F' c - x) = (minpoly F x).eval c := by
  set y := x - algebraMap F F' c with hy
  have hyint : IsIntegral F y := Algebra.IsIntegral.isIntegral y
  have hminy : minpoly F y = (minpoly F x).comp (X + C c) := minpoly.sub_algebraMap x c
  have hdegy : (minpoly F y).natDegree = Module.finrank F F' := by
    rw [hminy, natDegree_comp, natDegree_X_add_C, mul_one, hdeg]
  have htower : Module.finrank F F' = Module.finrank F F⟮y⟯ * Module.finrank F⟮y⟯ F' :=
    (Module.finrank_mul_finrank F F⟮y⟯ F').symm
  rw [adjoin.finrank hyint, hdegy] at htower
  have hn : 0 < Module.finrank F F' := Module.finrank_pos
  have hm : Module.finrank F⟮y⟯ F' = 1 := by
    have h : Module.finrank F F' * Module.finrank F⟮y⟯ F' = Module.finrank F F' * 1 := by
      rw [mul_one]; exact htower.symm
    exact Nat.eq_of_mul_eq_mul_left hn h
  have hnormy : Algebra.norm F y = (-1) ^ Module.finrank F F' * (minpoly F x).eval c := by
    rw [Algebra.norm_eq_norm_adjoin, hm, pow_one, ← adjoin.powerBasis_gen hyint,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, adjoin.powerBasis_gen, minpoly_gen,
        adjoin.powerBasis_dim,
      hdegy, hminy, coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_C, zero_add]
  have hneg : algebraMap F F' c - x = algebraMap F F' (-1) * y := by
    rw [map_neg, map_one, neg_one_mul, hy, neg_sub]
  rw [hneg, map_mul, Algebra.norm_algebraMap, hnormy, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg,
    one_pow,
    one_mul]

end Norm


end S09NR

theorem _root_.Algebra.norm_algebraMap_sub_eq_minpoly_eval {F F' : Type*} [Field F] [Field F']
  [Algebra F F'] [Module.Finite F F'] (x : F') (hdeg : (minpoly F x).natDegree = Module.finrank F
  F') (c : F) : Algebra.norm F (algebraMap F F' c - x) = (minpoly F x).eval c := by
  exact S09NR.norm_algebraMap_sub x hdeg c
end AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_norm_algebraMap_sub_eq_minpoly_eval
end ProofImplementation

end Algebra_norm_algebraMap_sub_eq_minpoly_eval

section Algebra_norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap

/-!
# Algebra norm eq pow finrank of is Nilpotent sub algebra Map
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Algebra_norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap

theorem _root_.Algebra.norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap {R A : Type*} [CommRing R]
  [IsDomain R] [Ring A] [Algebra R A] [Module.Free R A] [Module.Finite R A] {a : A} {μ : R} (h :
  IsNilpotent (a - algebraMap R A μ)) : Algebra.norm R a = μ ^ Module.finrank R A := by
  have hN : IsNilpotent (Algebra.lmul R A (a - algebraMap R A μ)) := by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [← map_pow, hk, map_zero]⟩
  have hN' : IsNilpotent (-(Algebra.lmul R A (a - algebraMap R A μ))) := hN.neg
  have hsplit : (Algebra.lmul R A) a
      = algebraMap R (Module.End R A) μ - (-(Algebra.lmul R A (a - algebraMap R A μ))) := by
    rw [sub_neg_eq_add, ← (Algebra.lmul R A).commutes μ, ← map_add]
    congr 1
    abel
  rw [Algebra.norm_apply, hsplit, ← LinearMap.eval_charpoly,
    IsNilpotent.charpoly_eq_X_pow_finrank hN', Polynomial.eval_pow, Polynomial.eval_X]
end Algebra_norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation

end Algebra_norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap

section Algebra_norm_one_add_eps_tmul

/-!
# Algebra norm one add eps tmul
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_norm_one_add_eps_tmul

universe u

open scoped TensorProduct

theorem _root_.Algebra.norm_one_add_eps_tmul
    (A' B : Type u) [CommRing A'] [CommRing B] [Algebra A' B] [Module.Free A' B] [Module.Finite A'
      B] (f : B) :
    Algebra.norm (DualNumber A') ((1 : DualNumber A' ⊗[A'] B) + (DualNumber.eps : DualNumber A')
      ⊗ₜ[A'] f) =
      1 + TrivSqZeroExt.inr (Algebra.trace A' B f) := by
  classical
  let b := Module.Free.chooseBasis A' B
  let b' : Module.Basis (Module.Free.ChooseBasisIndex A' B) (DualNumber A') (DualNumber A' ⊗[A'] B)
    :=
    Algebra.TensorProduct.basis (DualNumber A') b
  have hM : ∀ g : B, Algebra.leftMulMatrix b' ((1 : DualNumber A') ⊗ₜ[A'] g)
      = (Algebra.leftMulMatrix b g).map (algebraMap A' (DualNumber A')) := by
    intro g
    have hlmul : Algebra.lmul (DualNumber A') (DualNumber A' ⊗[A'] B) ((1 : DualNumber A') ⊗ₜ[A'] g)
        = (Algebra.lmul A' B g).baseChange (DualNumber A') := by
      apply b'.ext
      intro k
      simp [b', Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
    rw [Algebra.leftMulMatrix_apply, hlmul, LinearMap.toMatrix_baseChange,
      Algebra.leftMulMatrix_apply]
  have hone : Algebra.leftMulMatrix (R := DualNumber A') (S := DualNumber A' ⊗[A'] B) b' 1 = 1 := by
    rw [Algebra.TensorProduct.one_def, hM 1, map_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have h1 : (DualNumber.eps : DualNumber A') ⊗ₜ[A'] f
      = (DualNumber.eps : DualNumber A') • ((1 : DualNumber A') ⊗ₜ[A'] f) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hadd : Algebra.leftMulMatrix b' ((1 : DualNumber A' ⊗[A'] B) + (DualNumber.eps : DualNumber
    A') ⊗ₜ[A'] f)
      = 1 + (DualNumber.eps : DualNumber A') • (Algebra.leftMulMatrix b f).map (algebraMap A'
        (DualNumber A')) := by
    rw [h1]
    simp only [map_add, map_smul, hone, hM]
  rw [Algebra.norm_eq_matrix_det b', hadd, Matrix.det_one_add_smul,
    pow_two, DualNumber.eps_mul_eps, mul_zero, add_zero,
    ← AddMonoidHom.map_trace (algebraMap A' (DualNumber A')), ← Algebra.trace_eq_matrix_trace b f,
    DualNumber.inr_eq_smul_eps]
  exact congrArg (fun z : DualNumber A' => 1 + z)
    (Algebra.smul_def (R := A') (A := DualNumber A')
      (Algebra.trace A' B f) DualNumber.eps).symm
end AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_norm_one_add_eps_tmul
end ProofImplementation

end Algebra_norm_one_add_eps_tmul

section Algebra_norm_one_tmul_eq_algebraMap_norm

/-!
# Algebra norm one tmul eq algebra Map norm
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_norm_one_tmul_eq_algebraMap_norm

universe u v w

open scoped TensorProduct

theorem _root_.Algebra.norm_one_tmul_eq_algebraMap_norm
    {K : Type u} [CommRing K] {L : Type v} [Ring L] [Algebra K L] [Module.Free K L] [Module.Finite
      K L]
    (K' : Type w) [CommRing K'] [Algebra K K'] (x : L) :
    Algebra.norm K' ((1 : K') ⊗ₜ[K] x : K' ⊗[K] L) = algebraMap K K' (Algebra.norm K x) := by
  classical
  rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  apply LinearMap.ext
  intro y
  induction y using TensorProduct.inductionOn with
  | tmul c l => simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  | add y z hy hz => simp only [map_add, hy, hz]
end AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_norm_one_tmul_eq_algebraMap_norm
end ProofImplementation

end Algebra_norm_one_tmul_eq_algebraMap_norm

section Algebra_exists_monoidHom_algebraMap_eq_norm_of_isIntegrallyClosed

/-!
# Algebra exists monoid Hom algebra Map eq norm of is Integrally Closed
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.AlgebraExistsMonoidHomAlgebraMap

universe u v w w'

theorem _root_.Algebra.exists_monoidHom_algebraMap_eq_norm_of_isIntegrallyClosed
    {A : Type u} {B : Type v} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B]
      [Algebra A B]
    [Algebra.IsIntegral A B]
    (K : Type w) (L : Type w') [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] :
    ∃ N : B →* A, ∀ b : B, algebraMap A K (N b) = Algebra.norm K (algebraMap B L b) := by
  classical
  have hmem : ∀ b : B, ∃ a : A, algebraMap A K a = Algebra.norm K (algebraMap B L b) := by
    intro b
    have hb : IsIntegral A (algebraMap B L b) := (Algebra.IsIntegral.isIntegral (R := A)
      b).algebraMap
    have hn : IsIntegral A (Algebra.norm K (algebraMap B L b)) := Algebra.isIntegral_norm K hb
    exact IsIntegrallyClosed.isIntegral_iff.mp hn
  choose N hN using hmem
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  refine ⟨{ toFun := N, map_one' := ?_, map_mul' := ?_ }, fun b => hN b⟩
  · apply hinj
    rw [hN, map_one, map_one, map_one]
  · intro b c
    apply hinj
    rw [hN, map_mul, map_mul, map_mul, hN, hN]
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.AlgebraExistsMonoidHomAlgebraMap
end ProofImplementation

end Algebra_exists_monoidHom_algebraMap_eq_norm_of_isIntegrallyClosed

section Algebra_norm_algebraMap_sub_eq_eval_minpoly_pow

/-!
# Algebra norm algebra Map sub eq eval minpoly pow
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_norm_algebraMap_sub_eq_eval_minpoly_pow
open Polynomial

theorem _root_.Algebra.norm_algebraMap_sub_eq_eval_minpoly_pow
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (x : L) (c : K) :
    Algebra.norm K (algebraMap K L c - x)
      = ((minpoly K x).eval c) ^ (Module.finrank K L / (minpoly K x).natDegree) := by
  have hx : IsIntegral K x := .of_finite K x
  have hmin : minpoly K (IntermediateField.AdjoinSimple.gen K x) = minpoly K x :=
    IntermediateField.minpoly_gen K x
  have hfinE : Module.finrank K (IntermediateField.adjoin K ({x} : Set L)) = (minpoly K
    x).natDegree :=
    IntermediateField.adjoin.finrank hx
  have hdeg : (minpoly K (IntermediateField.AdjoinSimple.gen K x)).natDegree
      = Module.finrank K (IntermediateField.adjoin K ({x} : Set L)) := by
    rw [hmin, hfinE]
  have h1 : Algebra.norm K (algebraMap K (IntermediateField.adjoin K ({x} : Set L)) c
      - IntermediateField.AdjoinSimple.gen K x) = (minpoly K x).eval c := by
    rw [Algebra.norm_algebraMap_sub_eq_minpoly_eval _ hdeg c, hmin]
  have h2 : algebraMap (IntermediateField.adjoin K ({x} : Set L)) L
      (algebraMap K (IntermediateField.adjoin K ({x} : Set L)) c
        - IntermediateField.AdjoinSimple.gen K x) = algebraMap K L c - x := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply, IntermediateField.AdjoinSimple.algebraMap_gen]
  have hn : Module.finrank (IntermediateField.adjoin K ({x} : Set L)) L
      = Module.finrank K L / (minpoly K x).natDegree := by
    have hmul := Module.finrank_mul_finrank K (IntermediateField.adjoin K ({x} : Set L)) L
    rw [hfinE] at hmul
    rw [← hmul, Nat.mul_div_cancel_left _ (minpoly.natDegree_pos hx)]
  rw [← h2, ← Algebra.norm_norm (S := IntermediateField.adjoin K ({x} : Set L)),
    Algebra.norm_algebraMap, map_pow, h1, hn]

end AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_norm_algebraMap_sub_eq_eval_minpoly_pow
end ProofImplementation

end Algebra_norm_algebraMap_sub_eq_eval_minpoly_pow

section Algebra_norm_algebraMap_eq_of_isPushout_of_isFractionRing

/-!
# Algebra norm algebra Map eq of is Pushout of is Fraction Ring
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.AlgebraNormAlgebraMapIsPushoutIs

universe u

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Algebra

export _root_.Algebra (IsPushout algebraMap norm_eq_of_algEquiv norm algebraMapSubmonoid
  IsPushout.equiv IsPushout.symm IsIntegral.of_finite IsAlgebraic.isAlgebraic
  IsIntegral.isAlgebraic IsPushout.comp_iff IsPushout.equiv_tmul TensorProduct.rightAlgebra
  norm_one_tmul_eq_algebraMap_norm)

namespace NormBaseChange

open _root_.Algebra


theorem isLocalization_of_finite (A B L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain
  B] [Algebra A B]
    [Module.Finite A B] [Field L] [Algebra B L] [IsFractionRing B L] (h : Function.Injective
      (algebraMap A B)) :
    IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L := by
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite _ _
  have : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
  refine (IsLocalization.iff_of_le_of_exists_dvd (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
    (nonZeroDivisors B) ?_ ?_).mpr inferInstance
  · rintro _ ⟨r, hr, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    rw [map_ne_zero_iff _ h]
    exact nonZeroDivisors.ne_zero hr
  · intro n hn
    obtain ⟨r, hr, hdvd⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A) n).exists_ne_zero_dvd hn
    exact ⟨algebraMap _ _ r, ⟨r, mem_nonZeroDivisors_of_ne_zero hr, rfl⟩, hdvd⟩

theorem isPushout_of_finite (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra A B]
    [Module.Finite A B] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra B L]
      [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] (h :
      Function.Injective (algebraMap A B)) :
    Algebra.IsPushout A K B L :=
  ⟨(isLocalizedModule_iff_isBaseChange (nonZeroDivisors A) K _).mp
    (isLocalizedModule_iff_isLocalization.mpr (isLocalization_of_finite A B L h))⟩

end Algebra.NormBaseChange

open Algebra.NormBaseChange in
theorem _root_.Algebra.norm_algebraMap_eq_of_isPushout_of_isFractionRing
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [IsDomain A] [IsDomain B] [IsDomain A'] [IsDomain B']
    [Algebra A B] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [Algebra.IsPushout A B A' B']
    [Module.Finite A B] (hAB : Function.Injective (algebraMap A B)) (hA'B' : Function.Injective
      (algebraMap A' B'))
    (K L K' L' : Type u) [Field K] [Field L] [Field K'] [Field L']
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra A' K'] [IsFractionRing A' K'] [Algebra B' L'] [IsFractionRing B' L']
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [Algebra K' L'] [Algebra A' L'] [IsScalarTower A' K' L'] [IsScalarTower A' B' L']
    (φ : K →+* K') (hφ : φ.comp (algebraMap A K) = (algebraMap A' K').comp (algebraMap A A'))
    (b : B) :
    φ (Algebra.norm K (algebraMap B L b)) = Algebra.norm K' (algebraMap B' L' (algebraMap B B' b))
      := by
  classical
  let algKK' : Algebra K K' := φ.toAlgebra
  let algAK' : Algebra A K' := ((algebraMap A' K').comp (algebraMap A A')).toAlgebra
  have : IsScalarTower A A' K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A K K' := IsScalarTower.of_algebraMap_eq fun a => (RingHom.congr_fun hφ
    a).symm
  let algBL' : Algebra B L' := ((algebraMap B' L').comp (algebraMap B B')).toAlgebra
  have : IsScalarTower B B' L' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let algAL' : Algebra A L' := ((algebraMap A' L').comp (algebraMap A A')).toAlgebra
  have : IsScalarTower A A' L' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A K' L' := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A' L' (algebraMap A A' a) = algebraMap K' L' (algebraMap A' K' (algebraMap A
      A' a))
    rw [IsScalarTower.algebraMap_apply A' K' L']
  have : IsScalarTower A B L' := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A' L' (algebraMap A A' a) = algebraMap B' L' (algebraMap B B' (algebraMap A
      B a))
    rw [IsScalarTower.algebraMap_apply A' B' L', ← IsScalarTower.algebraMap_apply A A' B',
      IsScalarTower.algebraMap_apply A B B']
  have : IsScalarTower A B' L' := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A' L' (algebraMap A A' a) = algebraMap B' L' (algebraMap A B' a)
    rw [IsScalarTower.algebraMap_apply A' B' L', ← IsScalarTower.algebraMap_apply A A' B']
  let algBT : Algebra B (K' ⊗[K] L) := ((algebraMap L (K' ⊗[K] L)).comp (algebraMap B L)).toAlgebra
  have : IsScalarTower B L (K' ⊗[K] L) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hAKT : ∀ a : A, algebraMap A (K' ⊗[K] L) a = algebraMap K (K' ⊗[K] L) (algebraMap A K a) :=
    fun a => by
    rw [IsScalarTower.algebraMap_apply A K' (K' ⊗[K] L), IsScalarTower.algebraMap_apply A K K',
      ← IsScalarTower.algebraMap_apply K K' (K' ⊗[K] L)]
  have : IsScalarTower A K (K' ⊗[K] L) := IsScalarTower.of_algebraMap_eq hAKT
  have : IsScalarTower A B (K' ⊗[K] L) := IsScalarTower.of_algebraMap_eq fun a => by
    rw [hAKT, IsScalarTower.algebraMap_apply B L (K' ⊗[K] L), ← IsScalarTower.algebraMap_apply A B
      L,
      IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply K L (K' ⊗[K] L)]
  have : IsScalarTower A L (K' ⊗[K] L) := IsScalarTower.of_algebraMap_eq fun a => by
    rw [hAKT, IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply K L (K' ⊗[K]
      L)]
  have : Algebra.IsPushout A A' B B' := Algebra.IsPushout.symm inferInstance
  have : Module.Finite A' B' :=
    Module.Finite.equiv (R := A') (Algebra.IsPushout.equiv A A' B B').toLinearEquiv
  have P1 : Algebra.IsPushout A K B L := isPushout_of_finite A B K L hAB
  have P2 : Algebra.IsPushout A' K' B' L' := isPushout_of_finite A' B' K' L' hA'B'
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L :=
    isLocalization_of_finite A B L hAB
  have : Module.Finite K L := Module.Finite.of_isLocalization A B (nonZeroDivisors A)
  have : Module.Free K L := Module.Free.of_divisionRing K L
  have big1 : Algebra.IsPushout A K' B L' := (Algebra.IsPushout.comp_iff A A' B B').mpr P2
  have := P1
  have big2 : Algebra.IsPushout A K' B (K' ⊗[K] L) := (Algebra.IsPushout.comp_iff A K B L).mpr
    inferInstance
  let e₁ : TensorProduct A K' B ≃ₐ[K'] L' := @Algebra.IsPushout.equiv A K' _ _ _ B L' _ _ _ _ _ _
    _ _ big1
  let e₂ : TensorProduct A K' B ≃ₐ[K'] (K' ⊗[K] L) := @Algebra.IsPushout.equiv A K' _ _ _ B (K'
    ⊗[K] L) _ _ _ _ _ _ _ _ big2
  have h1 : e₁ ((1 : K') ⊗ₜ[A] b) = algebraMap B' L' (algebraMap B B' b) := by
    change Algebra.IsPushout.equiv A K' B L' ((1 : K') ⊗ₜ[A] b) = _
    rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul]; rfl
  have h2 : e₂ ((1 : K') ⊗ₜ[A] b) = (1 : K') ⊗ₜ[K] algebraMap B L b := by
    change Algebra.IsPushout.equiv A K' B (K' ⊗[K] L) ((1 : K') ⊗ₜ[A] b) = _
    rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul]; rfl
  calc φ (Algebra.norm K (algebraMap B L b))
      = algebraMap K K' (Algebra.norm K (algebraMap B L b)) := rfl
    _ = Algebra.norm K' ((1 : K') ⊗ₜ[K] algebraMap B L b) :=
      (Algebra.norm_one_tmul_eq_algebraMap_norm K' _).symm
    _ = Algebra.norm K' ((e₂.symm.trans e₁) ((1 : K') ⊗ₜ[K] algebraMap B L b)) :=
      (Algebra.norm_eq_of_algEquiv _ _).symm
    _ = Algebra.norm K' (algebraMap B' L' (algebraMap B B' b)) := by
        congr 1
        change e₁ (e₂.symm ((1 : K') ⊗ₜ[K] algebraMap B L b)) = _
        rw [← h2, AlgEquiv.symm_apply_apply, h1]
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.AlgebraNormAlgebraMapIsPushoutIs
end ProofImplementation

end Algebra_norm_algebraMap_eq_of_isPushout_of_isFractionRing

section Algebra_algebraMap_norm_eq_norm_mul_norm_of_adjoin_eq_top

/-!
# Algebra algebra Map norm eq norm mul norm of adjoin eq top
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Algebra_algebraMap_norm_eq_norm_mul_norm_of_adjoin_eq_top

open scoped TensorProduct

namespace NormSplit

theorem surjective_of_adjoin_eq_top
    {F F₁ F₂ E : Type*} [Field F] [Field F₁] [Field F₂] [Field E]
    [Algebra F F₁] [Algebra F F₂] [Algebra F E] [Algebra F₁ E] [Algebra F₂ E]
    [IsScalarTower F F₁ E] [IsScalarTower F F₂ E]
    (μ : F₂ ⊗[F] F₁ →ₐ[F₂] E)
    (hμ : ∀ (a : F₂) (b : F₁), μ (a ⊗ₜ b) = algebraMap F₂ E a * algebraMap F₁ E b)
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤) :
    Function.Surjective μ := by
  intro z
  have hz : z ∈ Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) :=
    hgen ▸ Algebra.mem_top
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨b, rfl⟩ | ⟨a, rfl⟩
    · exact ⟨1 ⊗ₜ b, by rw [hμ, map_one, one_mul]⟩
    · exact ⟨a ⊗ₜ 1, by rw [hμ, map_one, mul_one]⟩
  | algebraMap r =>
    refine ⟨algebraMap F₂ (F₂ ⊗[F] F₁) (algebraMap F F₂ r), ?_⟩
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  | add x y _ _ hx hy =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    exact ⟨p + q, map_add μ p q⟩
  | mul x y _ _ hx hy =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    exact ⟨p * q, map_mul μ p q⟩

end NormSplit

theorem _root_.Algebra.algebraMap_norm_eq_norm_mul_norm_of_adjoin_eq_top
    {F F₁ F₂ Z Z' : Type*} [Field F] [Field F₁] [Field F₂] [Field Z] [Field Z']
    [Algebra F F₁] [Algebra F F₂]
    [Algebra F Z] [Algebra F₁ Z] [Algebra F₂ Z] [IsScalarTower F F₁ Z] [IsScalarTower F F₂ Z]
    [Algebra F Z'] [Algebra F₁ Z'] [Algebra F₂ Z'] [IsScalarTower F F₁ Z'] [IsScalarTower F F₂ Z']
    [FiniteDimensional F F₁] [FiniteDimensional F F₂]
    [FiniteDimensional F₁ Z] [FiniteDimensional F₁ Z']
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ Z) ∪ Set.range (algebraMap F₂ Z)) = ⊤)
    (hgen' : Algebra.adjoin F (Set.range (algebraMap F₁ Z') ∪ Set.range (algebraMap F₂ Z')) = ⊤)
    (hdeg : Module.finrank F₁ Z + Module.finrank F₁ Z' = Module.finrank F F₂)
    (hne : ∃ (a : F₂) (b : F₁), algebraMap F₂ Z' a = algebraMap F₁ Z' b ∧
      algebraMap F₂ Z a ≠ algebraMap F₁ Z b)
    (g : F₁) :
    algebraMap F F₂ (Algebra.norm F g)
      = Algebra.norm F₂ (algebraMap F₁ Z g) * Algebra.norm F₂ (algebraMap F₁ Z' g) := by
  classical
  have : FiniteDimensional F Z := Module.Finite.trans F₁ Z
  have : FiniteDimensional F Z' := Module.Finite.trans F₁ Z'
  have : FiniteDimensional F₂ Z := Module.Finite.of_restrictScalars_finite F F₂ Z
  have : FiniteDimensional F₂ Z' := Module.Finite.of_restrictScalars_finite F F₂ Z'
  have hdeg₂ : Module.finrank F₂ Z + Module.finrank F₂ Z' = Module.finrank F F₁ := by
    have hZ := Module.finrank_mul_finrank F F₁ Z
    have hZ₂ := Module.finrank_mul_finrank F F₂ Z
    have hZ' := Module.finrank_mul_finrank F F₁ Z'
    have hZ'₂ := Module.finrank_mul_finrank F F₂ Z'
    have h2 : 0 < Module.finrank F F₂ := Module.finrank_pos
    have key : (Module.finrank F₂ Z + Module.finrank F₂ Z') * Module.finrank F F₂
        = Module.finrank F F₁ * Module.finrank F F₂ := by
      calc (Module.finrank F₂ Z + Module.finrank F₂ Z') * Module.finrank F F₂
          = Module.finrank F Z + Module.finrank F Z' :=
            by rw [add_mul, mul_comm, hZ₂, mul_comm, hZ'₂]
        _ = Module.finrank F F₁ * (Module.finrank F₁ Z + Module.finrank F₁ Z') := by
            rw [mul_add, hZ, hZ']
        _ = Module.finrank F F₁ * Module.finrank F F₂ := by rw [hdeg]
    exact Nat.eq_of_mul_eq_mul_right h2 key
  let m : (F₂ ⊗[F] F₁) →ₐ[F₂] Z := Algebra.TensorProduct.lift (Algebra.ofId F₂ Z)
    (IsScalarTower.toAlgHom F F₁ Z) (fun _ _ => Commute.all _ _)
  let m' : (F₂ ⊗[F] F₁) →ₐ[F₂] Z' := Algebra.TensorProduct.lift (Algebra.ofId F₂ Z')
    (IsScalarTower.toAlgHom F F₁ Z') (fun _ _ => Commute.all _ _)
  have hm : ∀ (a : F₂) (b : F₁), m (a ⊗ₜ b) = algebraMap F₂ Z a * algebraMap F₁ Z b := fun a b =>
    Algebra.TensorProduct.lift_tmul _ _ _ a b
  have hm' : ∀ (a : F₂) (b : F₁), m' (a ⊗ₜ b) = algebraMap F₂ Z' a * algebraMap F₁ Z' b := fun a b
    =>
    Algebra.TensorProduct.lift_tmul _ _ _ a b
  have hsurj : Function.Surjective m := NormSplit.surjective_of_adjoin_eq_top m hm hgen
  have hsurj' : Function.Surjective m' := NormSplit.surjective_of_adjoin_eq_top m' hm' hgen'
  have hI : (RingHom.ker m).IsMaximal := RingHom.ker_isMaximal_of_surjective m hsurj
  have hJ : (RingHom.ker m').IsMaximal := RingHom.ker_isMaximal_of_surjective m' hsurj'
  have hIJ : RingHom.ker m ≠ RingHom.ker m' := by
    obtain ⟨a, b, hab', hab⟩ := hne
    intro h
    have hx : (a ⊗ₜ (1 : F₁) - (1 : F₂) ⊗ₜ b : (F₂ ⊗[F] F₁)) ∈ RingHom.ker m' := by
      rw [RingHom.mem_ker, map_sub, hm', hm', map_one, map_one, mul_one, one_mul, hab', sub_self]
    rw [← h, RingHom.mem_ker, map_sub, hm, hm, map_one, map_one, mul_one, one_mul, sub_eq_zero]
      at hx
    exact hab hx
  have hsup : RingHom.ker m ⊔ RingHom.ker m' = ⊤ := Ideal.IsMaximal.coprime_of_ne hI hJ hIJ
  let e : (F₂ ⊗[F] F₁) →ₐ[F₂] Z × Z' := m.prod m'
  have he : ∀ x, e x = (m x, m' x) := fun x => rfl
  have hesurj : Function.Surjective e := by
    rintro ⟨z, z'⟩
    obtain ⟨p, rfl⟩ := hsurj z
    obtain ⟨q, rfl⟩ := hsurj' z'
    have h1 : (1 : (F₂ ⊗[F] F₁)) ∈ RingHom.ker m ⊔ RingHom.ker m' := hsup ▸ Submodule.mem_top
    obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp h1
    refine ⟨p * j + q * i, ?_⟩
    rw [RingHom.mem_ker] at hi hj
    have hmj : m j = 1 := by
      have := congrArg m hij; rw [map_add, hi, zero_add, map_one] at this; exact this
    have hm'i : m' i = 1 := by
      have := congrArg m' hij; rw [map_add, hj, add_zero, map_one] at this; exact this
    rw [he, Prod.mk.injEq, map_add, map_add, map_mul, map_mul, map_mul, map_mul, hi, hj, hmj, hm'i]
    constructor <;> ring
  have hdim : Module.finrank F₂ (F₂ ⊗[F] F₁) = Module.finrank F₂ (Z × Z') := by
    rw [Module.finrank_prod, hdeg₂, Module.finrank_baseChange]
  have heinj : Function.Injective e :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := e.toLinearMap)).mpr hesurj
  let ε : (F₂ ⊗[F] F₁) ≃ₐ[F₂] Z × Z' := AlgEquiv.ofBijective e ⟨heinj, hesurj⟩
  have hε : ε (1 ⊗ₜ g) = (algebraMap F₁ Z g, algebraMap F₁ Z' g) := by
    change e (1 ⊗ₜ g) = _
    rw [he, hm, hm', map_one, map_one, one_mul, one_mul]
  have hN1 : Algebra.norm F₂ ((1 : F₂) ⊗ₜ[F] g : (F₂ ⊗[F] F₁))
      = Algebra.norm F₂ (algebraMap F₁ Z g) * Algebra.norm F₂ (algebraMap F₁ Z' g) := by
    rw [← Algebra.norm_eq_of_algEquiv ε, hε, Algebra.norm_prod]
  have hN2 : Algebra.norm F₂ ((1 : F₂) ⊗ₜ[F] g : (F₂ ⊗[F] F₁)) = algebraMap F F₂ (Algebra.norm F g)
    := by
    rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange (A := F₂)]
    congr 1
    refine TensorProduct.AlgebraTensorModule.ext fun a b => ?_
    rw [LinearMap.baseChange_tmul]
    change ((1 : F₂) ⊗ₜ[F] g) * (a ⊗ₜ[F] b) = a ⊗ₜ[F] (g * b)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [← hN2, hN1]
end Algebra_algebraMap_norm_eq_norm_mul_norm_of_adjoin_eq_top
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation

end Algebra_algebraMap_norm_eq_norm_mul_norm_of_adjoin_eq_top

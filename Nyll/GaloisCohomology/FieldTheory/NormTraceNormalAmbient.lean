/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Trace.Basic

/-!
# Norm and trace through a finite normal ambient field

Every embedding of the source into an algebraic closure extends to an
automorphism of the normal ambient field. The norm product and trace sum use
the same embeddings, including when the source extension is not Galois.
-/

@[expose] public section

namespace Algebra

universe u v w

open scoped BigOperators

variable (K : Type u) (L : Type v) (E : Type w)
    [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [FiniteDimensional K E] [Normal K E]

omit [FiniteDimensional K E] in
/-- The actual norm is the product of all lifted embeddings in a normal
ambient field. The source extension need only be separable. -/
theorem norm_eq_prod_liftNormal (x : L) :
    algebraMap K E (Algebra.norm K x) =
      ∏ σ : L →ₐ[K] AlgebraicClosure E,
        (σ.liftNormal (AlgebraicClosure E)).restrictNormal' E (algebraMap L E x) := by
  classical
  apply (algebraMap E (AlgebraicClosure E)).injective
  rw [← IsScalarTower.algebraMap_apply K E (AlgebraicClosure E),
    Algebra.norm_eq_prod_embeddings, map_prod]
  apply Finset.prod_congr rfl
  intro σ _
  change σ x = algebraMap E (AlgebraicClosure E)
    ((σ.liftNormal (AlgebraicClosure E)).restrictNormal E (algebraMap L E x))
  rw [AlgHom.restrictNormal_commutes,
    ← IsScalarTower.algebraMap_apply L E (AlgebraicClosure E),
    AlgHom.liftNormal_commutes, algebraMap_self, RingHom.id_apply]

omit [FiniteDimensional K E] in
/-- The actual trace is the sum indexed by exactly the same lifted embeddings
as the norm product. -/
theorem trace_eq_sum_liftNormal (x : L) :
    algebraMap K E (Algebra.trace K L x) =
      ∑ σ : L →ₐ[K] AlgebraicClosure E,
        (σ.liftNormal (AlgebraicClosure E)).restrictNormal' E (algebraMap L E x) := by
  classical
  apply (algebraMap E (AlgebraicClosure E)).injective
  rw [← IsScalarTower.algebraMap_apply K E (AlgebraicClosure E),
    _root_.trace_eq_sum_embeddings (AlgebraicClosure E), map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  change σ x = algebraMap E (AlgebraicClosure E)
    ((σ.liftNormal (AlgebraicClosure E)).restrictNormal E (algebraMap L E x))
  rw [AlgHom.restrictNormal_commutes,
    ← IsScalarTower.algebraMap_apply L E (AlgebraicClosure E),
    AlgHom.liftNormal_commutes, algebraMap_self, RingHom.id_apply]

end Algebra

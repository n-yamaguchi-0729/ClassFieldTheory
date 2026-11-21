/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
Adapted from TauCeti/FieldTheory/Galois/Minpoly.lean at ca32605ff53921fa0689dd312618b7cfaafa7e43.
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Minpoly.ConjRootClass

/-! # The evaluated derivative of a Galois primitive polynomial -/

@[expose] public section

open Polynomial IntermediateField

namespace RamificationTheory

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

private theorem minpoly_map_eq_prod_galois_linearFactors {x : L} (hx : K⟮x⟯ = ⊤) :
    (minpoly K x).map (algebraMap K L) = ∏ σ : L ≃ₐ[K] L, (X - C (σ x)) := by
  classical
  have hinj : Function.Injective fun σ : L ≃ₐ[K] L => σ x := fun σ τ h =>
    AlgEquiv.coe_toAlgHom_injective (AlgHom.ext_of_adjoin_eq_top
      ((adjoin_eq_top_iff_of_isAlgebraic fun y _ => IsAlgebraic.of_finite K y).mp hx)
      (Set.eqOn_singleton.mpr h))
  have hcarrier : (ConjRootClass.mk K x).carrier.toFinset =
      Finset.univ.image fun σ : L ≃ₐ[K] L => σ x := by
    ext y
    simp only [Set.mem_toFinset, ConjRootClass.mem_carrier, ConjRootClass.mk_eq_mk,
      isConjRoot_iff_exists_algEquiv, Finset.mem_image, Finset.mem_univ, true_and]
  rw [← ConjRootClass.minpoly_mk, ConjRootClass.minpoly.map_eq_prod, hcarrier,
    Finset.prod_image hinj.injOn]

/-- The derivative evaluated at a primitive element is the product of its differences
from the other Galois conjugates. -/
theorem aeval_derivative_minpoly_eq_prod_galois_displacements [DecidableEq (L ≃ₐ[K] L)]
    {x : L} (hx : K⟮x⟯ = ⊤) :
    aeval x (derivative (minpoly K x)) = ∏ σ ∈ Finset.univ.erase (1 : L ≃ₐ[K] L), (x - σ x) := by
  rw [← eval_map_algebraMap, ← derivative_map,
    minpoly_map_eq_prod_galois_linearFactors hx, derivative_prod_finset, eval_finsetSum,
    Fintype.sum_eq_single 1]
  · simp only [derivative_X_sub_C, mul_one, eval_prod, eval_sub, eval_X, eval_C]
  · intro σ hσ
    simp only [derivative_X_sub_C, mul_one, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hσ, Finset.mem_univ 1⟩)
      (sub_self x)

end RamificationTheory

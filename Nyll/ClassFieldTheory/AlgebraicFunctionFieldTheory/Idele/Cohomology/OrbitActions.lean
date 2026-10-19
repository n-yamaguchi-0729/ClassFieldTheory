/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.OrbitBlocks

/-!
# Galois actions on the actual completed orbit blocks

The finite fiber and restricted-product actions come from the actual action on
ideles. Their concrete comparisons with induced modules preserve that action
and identify integral fiber blocks with pointwise integral induced functions.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place RestrictedProduct

namespace FunctionField.IdeleGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The actual conjugation of an included finite block, projected to its fiber. -/
instance fiberSMul (v : Place k K) : SMul (L ≃ₐ[K] L) (FiberUnits (L := L) v) where
  smul σ x := fiberProjection (L := L) v (σ • fiberInclusion (L := L) v x)

/-- Projection to the fiber retains the induced function of an actual idele. -/
theorem fiberToInduced_projection (w : Place k L) (a : IdeleGroup k L) :
    fiberToInduced (K := K) w (fiberProjection (L := L) (w.restrict K) a) =
      ideleToInduced (K := K) w a :=
  ideleToInduced_fiberInclusion_projection (K := K) w a

/-- The actual finite-fiber comparison intertwines Galois conjugation and right translation. -/
theorem fiberInducedEquiv_smul (w : Place k L) (σ : L ≃ₐ[K] L)
    (x : FiberUnits (L := L) (w.restrict K)) :
    fiberInducedEquiv (K := K) w (σ • x) = σ • fiberInducedEquiv (K := K) w x := by
  change fiberToInduced (K := K) w
      (fiberProjection (L := L) (w.restrict K)
        (σ • fiberInclusion (L := L) (w.restrict K) x)) =
    σ • ideleToInduced (K := K) w (fiberInclusion (L := L) (w.restrict K) x)
  rw [fiberToInduced_projection]
  exact ideleToInduced_smul (K := K) w σ _

/-- The actual finite-fiber action satisfies the multiplicative action laws. -/
instance fiberMulDistribMulAction (v : Place k K) :
    MulDistribMulAction (L ≃ₐ[K] L) (FiberUnits (L := L) v) where
  smul := (· • ·)
  one_smul x := by
    obtain ⟨w, rfl⟩ := Place.exists_restrict_eq (M := L) v
    apply (fiberInducedEquiv (K := K) w).injective
    rw [fiberInducedEquiv_smul, one_smul]
  mul_smul σ τ x := by
    obtain ⟨w, rfl⟩ := Place.exists_restrict_eq (M := L) v
    apply (fiberInducedEquiv (K := K) w).injective
    rw [fiberInducedEquiv_smul, fiberInducedEquiv_smul, fiberInducedEquiv_smul, mul_smul]
  smul_one σ := by
    obtain ⟨w, rfl⟩ := Place.exists_restrict_eq (M := L) v
    apply (fiberInducedEquiv (K := K) w).injective
    rw [fiberInducedEquiv_smul, map_one, smul_one]
  smul_mul σ x y := by
    obtain ⟨w, rfl⟩ := Place.exists_restrict_eq (M := L) v
    apply (fiberInducedEquiv (K := K) w).injective
    rw [fiberInducedEquiv_smul, map_mul, map_mul,
      fiberInducedEquiv_smul, fiberInducedEquiv_smul, smul_mul']

/-- The completed fiber of a conjugated idele is the conjugated actual fiber. -/
theorem fiberProjection_smul (v : Place k K) (σ : L ≃ₐ[K] L) (a : IdeleGroup k L) :
    fiberProjection (L := L) v (σ • a) = σ • fiberProjection (L := L) v a := by
  obtain ⟨w, rfl⟩ := Place.exists_restrict_eq (M := L) v
  apply (fiberInducedEquiv (K := K) w).injective
  rw [fiberInducedEquiv_smul]
  change fiberToInduced (K := K) w (fiberProjection (L := L) (w.restrict K) (σ • a)) =
    σ • fiberToInduced (K := K) w (fiberProjection (L := L) (w.restrict K) a)
  rw [fiberToInduced_projection, fiberToInduced_projection]
  exact ideleToInduced_smul (K := K) w σ a

omit [Algebra k K] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L] in
private theorem component_smul_integral_iff (g : SemilinearAut k L)
    (a : IdeleGroup k L) (w : Place k L) :
    component w (g • a) ∈ w.adicCompletionIntegers.units ↔
      a (g⁻¹ • w) ∈ (g⁻¹ • w).adicCompletionIntegers.units := by
  have h := placeCompletionUnitsEquiv_mem_localUnits_iff g⁻¹ w
    ((placeCompletionUnitsEquiv g⁻¹ w).symm (a (g⁻¹ • w)))
  rw [ContinuousMulEquiv.apply_symm_apply] at h
  exact h.symm

/-- The induced comparison identifies actual integral fibers with pointwise integral functions. -/
theorem fiberInducedEquiv_integral_iff (w : Place k L)
    (x : FiberUnits (L := L) (w.restrict K)) :
    (∀ σ : L ≃ₐ[K] L,
      (fiberInducedEquiv (K := K) w x).1 σ ∈ w.adicCompletionIntegers.units) ↔
      x ∈ fiberIntegralUnits (L := L) (w.restrict K) := by
  constructor
  · intro hx u
    obtain ⟨τ, hτ⟩ := Place.exists_algEquiv_smul_eq_of_restrict_eq w u.1
      ((Place.mem_fiberOver (w.restrict K)).mp u.2)
    have h := (component_smul_integral_iff
      (SemilinearAut.ofAlgAut ((τ⁻¹).restrictScalars k))
      (fiberInclusion (L := L) (w.restrict K) x) w).mp (hx τ⁻¹)
    change fiberInclusion (L := L) (w.restrict K) x
        (SemilinearAut.ofAlgAut (τ.restrictScalars k) • w) ∈
      (SemilinearAut.ofAlgAut (τ.restrictScalars k) • w).adicCompletionIntegers.units at h
    rw [hτ] at h
    change component u.1 (fiberInclusion (L := L) (w.restrict K) x) ∈
      u.1.adicCompletionIntegers.units at h
    rwa [component_fiberInclusion] at h
  · intro hx σ
    apply (component_smul_integral_iff
      (SemilinearAut.ofAlgAut (σ.restrictScalars k))
      (fiberInclusion (L := L) (w.restrict K) x) w).mpr
    let q : (w.restrict K).fiberOver L :=
      ⟨(SemilinearAut.ofAlgAut (σ.restrictScalars k))⁻¹ • w,
        (Place.mem_fiberOver (w.restrict K)).mpr (Place.restrict_ofAlgAut_smul σ.symm w)⟩
    change component q.1 (fiberInclusion (L := L) (w.restrict K) x) ∈
      q.1.adicCompletionIntegers.units
    rw [component_fiberInclusion]
    exact hx q

/-- Regrouping the actual idele action supplies an action on the grouped restricted product. -/
instance fiberRestrictedProductSMul :
    SMul (L ≃ₐ[K] L) (FiberRestrictedProduct (k := k) (K := K) (L := L)) where
  smul σ a := groupByPlace (k := k) (K := K) (L := L)
    (σ • (groupByPlace (k := k) (K := K) (L := L)).symm a)

/-- The regrouped action retains all multiplicative action laws of actual ideles. -/
instance fiberRestrictedProductAction :
    MulDistribMulAction (L ≃ₐ[K] L) (FiberRestrictedProduct (k := k) (K := K) (L := L)) :=
  Function.Injective.mulDistribMulAction
    (groupByPlace (k := k) (K := K) (L := L)).symm.toMonoidHom
    (groupByPlace (k := k) (K := K) (L := L)).symm.injective
    (fun _ _ => (groupByPlace (k := k) (K := K) (L := L)).symm_apply_apply _)

/-- Regrouping actual ideles is Galois equivariant. -/
theorem groupByPlace_smul (σ : L ≃ₐ[K] L) (a : IdeleGroup k L) :
    groupByPlace (k := k) (K := K) (L := L) (σ • a) =
      σ • groupByPlace (k := k) (K := K) (L := L) a := by
  change groupByPlace (k := k) (K := K) (L := L) (σ • a) =
    groupByPlace (k := k) (K := K) (L := L)
      (σ • (groupByPlace (k := k) (K := K) (L := L)).symm
        (groupByPlace (k := k) (K := K) (L := L) a))
  rw [MulEquiv.symm_apply_apply]

/-- The regrouped actual action acts on each completed fiber through its actual fiber action. -/
theorem fiberRestrictedProduct_smul_apply (σ : L ≃ₐ[K] L)
    (a : FiberRestrictedProduct (k := k) (K := K) (L := L)) (v : Place k K) :
    (σ • a) v = σ • a v := by
  change fiberProjection (L := L) v
      (σ • (groupByPlace (k := k) (K := K) (L := L)).symm a) = σ • a v
  rw [fiberProjection_smul]
  congr 1
  exact congrArg (fun b : FiberRestrictedProduct (k := k) (K := K) (L := L) => b v)
    ((groupByPlace (k := k) (K := K) (L := L)).apply_symm_apply a)

end FunctionField.IdeleGroup

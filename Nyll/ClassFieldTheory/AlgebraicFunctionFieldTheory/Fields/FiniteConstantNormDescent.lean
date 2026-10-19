/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.GeometricConstantPolynomial
import Nyll.GaloisCohomology.FieldTheory.SimpleBaseChangeNorm
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Finite constant descent of actual norm equations

Tsen solves the norm equation over the geometric constant extension. Its solution
and minimal polynomial descend to a common finite constant extension. Preserving
the minimal polynomial identifies the actual field norms at that finite stage.
-/

noncomputable section

namespace FunctionField

open IntermediateField

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]

/-- Every norm equation in a finite simple extension has a solution after some
actual finite extension of the constants. -/
theorem exists_fullConstantDegreeStage_norm_preimage
    (α : Ω) (hα : IsIntegral K α) (a : K) :
    ∃ n : ℕ+, ∃ x : adjoin (fullConstantDegreeStage k K Ω (n : ℕ)) ({α} : Set Ω),
      Algebra.norm (fullConstantDegreeStage k K Ω (n : ℕ)) x =
        algebraMap K (fullConstantDegreeStage k K Ω (n : ℕ)) a := by
  let A := geometricConstantExtension k K Ω
  let M := adjoin A ({α} : Set Ω)
  have hfin : FiniteDimensional A M := adjoin.finiteDimensional hα.tower_top
  obtain ⟨x, hx⟩ := geometricConstantExtension_norm_surjective k K Ω M (algebraMap K A a)
  obtain ⟨n, h, hmin, hxB⟩ :=
    exists_fullConstantDegreeStage_minpoly_and_mem_adjoin k K Ω α (x : Ω) hα x.property
  let B := (fullConstantDegreeStage k K Ω (n : ℕ)).toIntermediateField
  let : Algebra B A := (inclusion h).toAlgebra
  have : IsScalarTower B A Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨n, ⟨(x : Ω), hxB⟩, ?_⟩
  apply (algebraMap B Ω).injective
  have hnorm := FieldTheory.norm_adjoin_simple_baseChange α (hα.tower_top (A := B))
    hmin (x : Ω) hxB x.property
  rw [← hnorm, hx, ← IsScalarTower.algebraMap_apply K A Ω,
    ← IsScalarTower.algebraMap_apply K B Ω]

/-- For a finite separable intermediate field, the solution lies in its actual
compositum with a finite constant extension. -/
theorem exists_fullConstantDegreeStage_compositum_norm_preimage
    (L : IntermediateField K Ω) [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (a : K) :
    ∃ n : ℕ+, ∃ x : adjoin (fullConstantDegreeStage k K Ω (n : ℕ)) (L : Set Ω),
      Algebra.norm (fullConstantDegreeStage k K Ω (n : ℕ)) x =
        algebraMap K (fullConstantDegreeStage k K Ω (n : ℕ)) a := by
  obtain ⟨α, hprim⟩ := Field.exists_primitive_element K L
  have hL : adjoin K ({(α : Ω)} : Set Ω) = L := by
    calc
      adjoin K ({(α : Ω)} : Set Ω) = IntermediateField.lift (adjoin K ({α} : Set L)) := by
        rw [lift_adjoin, Set.image_singleton]
      _ = L := by rw [hprim, lift_top]
  have hα : IsIntegral K (α : Ω) := (Algebra.IsIntegral.isIntegral (R := K) α).map L.val
  obtain ⟨n, x, hx⟩ := exists_fullConstantDegreeStage_norm_preimage k K Ω (α : Ω) hα a
  let B := fullConstantDegreeStage k K Ω (n : ℕ)
  have hgen : adjoin B (L : Set Ω) = adjoin B ({(α : Ω)} : Set Ω) := by
    calc
      adjoin B (L : Set Ω) = adjoin B (adjoin K ({(α : Ω)} : Set Ω) : Set Ω) :=
        congrArg (fun E : IntermediateField K Ω => adjoin B (E : Set Ω)) hL.symm
      _ = adjoin B ({(α : Ω)} : Set Ω) := adjoin_adjoin_right B ({(α : Ω)} : Set Ω)
  let e := IntermediateField.equivOfEq hgen.symm
  refine ⟨n, e x, ?_⟩
  rw [Algebra.norm_eq_of_algEquiv e, hx]

end FunctionField

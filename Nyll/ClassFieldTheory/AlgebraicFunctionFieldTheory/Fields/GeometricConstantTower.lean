/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.GeometricConstantExtension
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantClosure

/-!
# Finite-stage descent in the actual geometric constant extension

The finite constant extensions form a directed system whose union is the actual
geometric constant extension. Every finite set of its elements is therefore
contained in a single constructed finite constant stage.
-/

noncomputable section

namespace FunctionField

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω]

/-- Any two actual finite constant stages embed in a third stage. -/
theorem fullConstantDegreeStage_directed :
    Directed (· ≤ ·)
      (fun n : ℕ+ => (fullConstantDegreeStage k K Ω (n : ℕ)).toIntermediateField) := by
  intro n m
  refine ⟨n * m, ?_, ?_⟩
  · exact fullConstantDegreeStage_mono k K Ω (dvd_mul_right (n : ℕ) (m : ℕ))
  · exact fullConstantDegreeStage_mono k K Ω (dvd_mul_left (m : ℕ) (n : ℕ))

variable [Algebra k Ω] [IsScalarTower k K Ω]

/-- Enlarging the initial constants to the full constants gives the same geometric compositum. -/
theorem geometricConstantExtension_eq_iSup :
    geometricConstantExtension k K Ω =
      ⨆ n : ℕ+, (fullConstantDegreeStage k K Ω (n : ℕ)).toIntermediateField := by
  rw [iSup_fullConstantDegreeStage]
  change IntermediateField.adjoin K (separableClosure k Ω : Set Ω) = _
  rw [separableClosure.eq_restrictScalars_of_isSeparable k (algebraicClosure k K) Ω]
  rfl

/-- Each element of the actual geometric constant extension lies in a finite constant stage. -/
theorem mem_geometricConstantExtension_iff (x : Ω) :
    x ∈ geometricConstantExtension k K Ω ↔
      ∃ n : ℕ+, x ∈ (fullConstantDegreeStage k K Ω (n : ℕ)).toIntermediateField := by
  rw [geometricConstantExtension_eq_iSup, ← SetLike.mem_coe,
    IntermediateField.coe_iSup_of_directed (fullConstantDegreeStage_directed k K Ω),
    Set.mem_iUnion]
  rfl

/-- Finitely many geometric elements descend to one actual finite constant extension. -/
theorem exists_fullConstantDegreeStage_containing_finset (S : Finset Ω)
    (hS : ∀ x ∈ S, x ∈ geometricConstantExtension k K Ω) :
    ∃ n : ℕ+, ∀ x ∈ S, x ∈ (fullConstantDegreeStage k K Ω (n : ℕ)).toIntermediateField := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun x hx => (Finset.notMem_empty x hx).elim⟩
  | @insert x S hx ih =>
    obtain ⟨n, hn⟩ := (mem_geometricConstantExtension_iff k K Ω x).mp
      (hS x (Finset.mem_insert_self x S))
    obtain ⟨m, hm⟩ := ih (fun y hy => hS y (Finset.mem_insert_of_mem hy))
    obtain ⟨r, hrn, hrm⟩ := fullConstantDegreeStage_directed k K Ω n m
    refine ⟨r, fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hrn hn
    · exact hrm (hm y hy)

/-- A finitely generated intermediate field in the geometric extension descends to one stage. -/
theorem exists_fullConstantDegreeStage_of_fg (E : IntermediateField K Ω)
    (hE : E.FG) (hgeom : E ≤ geometricConstantExtension k K Ω) :
    ∃ n : ℕ+, E ≤ (fullConstantDegreeStage k K Ω (n : ℕ)).toIntermediateField := by
  obtain ⟨S, rfl⟩ := hE
  obtain ⟨n, hn⟩ := exists_fullConstantDegreeStage_containing_finset k K Ω S
    (fun x hx => hgeom (IntermediateField.subset_adjoin K (S : Set Ω) hx))
  exact ⟨n, IntermediateField.adjoin_le_iff.mpr hn⟩

/-- In particular every finite intermediate field of the geometric extension descends. -/
theorem exists_fullConstantDegreeStage_of_finite (E : IntermediateField K Ω)
    [FiniteDimensional K E] (hgeom : E ≤ geometricConstantExtension k K Ω) :
    ∃ n : ℕ+, E ≤ (fullConstantDegreeStage k K Ω (n : ℕ)).toIntermediateField := by
  exact exists_fullConstantDegreeStage_of_fg k K Ω E
    (IntermediateField.essFiniteType_iff.mp inferInstance) hgeom

end FunctionField

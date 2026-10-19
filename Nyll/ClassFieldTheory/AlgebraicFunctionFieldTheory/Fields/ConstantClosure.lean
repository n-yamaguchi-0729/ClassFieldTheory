/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.AbsoluteConstantDegree
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionTowerOrder

/-!
# Exhaustion of the actual maximal constant extension

Every algebraic constant belongs to the constructed finite field of its degree.
Consequently the actual maximal constant extension is the supremum of the finite
constant stages, and the kernel of arithmetic degree fixes all those stages.
-/

noncomputable section

namespace FunctionField

variable (k Ω : Type*) [Field k] [Finite k] [Field Ω] [Algebra k Ω] [IsSepClosed Ω]

/-- A finite field in the ambient closure embeds into the constructed field of
any degree divisible by its own degree, by its actual inclusion in the ambient field. -/
theorem le_finiteConstantsInClosure_of_finrank_dvd
    (C : IntermediateField k Ω) [FiniteDimensional k C] (n : ℕ) [NeZero n]
    (hn : Module.finrank k C ∣ n) :
    C ≤ (finiteConstantsInClosure k Ω n).toIntermediateField := by
  have : Finite C := Module.finite_of_finite k
  have : Finite (finiteConstantsInClosure k Ω n) := finite_finiteConstantsInClosure k Ω n
  have hd : Module.finrank k C ∣ Module.finrank k (finiteConstantsInClosure k Ω n) := by
    rw [finrank_finiteConstantsInClosure]
    exact hn
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hd
  let j : C →ₐ[k] Ω := (finiteConstantsInClosure k Ω n).toIntermediateField.val.comp f
  have hj : j.fieldRange = C := AlgHom.fieldRange_of_normal j
  intro x hx
  rw [← hj] at hx
  obtain ⟨y, hy⟩ := hx
  rw [← hy]
  exact (f y).property

/-- The finite constant stages exhaust the actual separable closure of a finite base. -/
theorem separableClosure_eq_iSup_finiteConstantsInClosure :
    separableClosure k Ω =
      ⨆ n : ℕ+, (finiteConstantsInClosure k Ω (n : ℕ)).toIntermediateField := by
  apply le_antisymm
  · intro c hc
    have hcsep := mem_separableClosure_iff.mp hc
    let C := IntermediateField.adjoin k ({c} : Set Ω)
    have : FiniteDimensional k C := IntermediateField.adjoin.finiteDimensional hcsep.isIntegral
    let n : ℕ+ := ⟨Module.finrank k C, Module.finrank_pos⟩
    have hC : C ≤ (finiteConstantsInClosure k Ω (n : ℕ)).toIntermediateField :=
      le_finiteConstantsInClosure_of_finrank_dvd k Ω C n dvd_rfl
    exact (le_iSup (fun n : ℕ+ =>
      (finiteConstantsInClosure k Ω (n : ℕ)).toIntermediateField) n)
        (hC (IntermediateField.subset_adjoin k _ (Set.mem_singleton c)))
  · apply iSup_le
    intro n
    exact (le_separableClosure_iff k Ω _).mpr inferInstance

end FunctionField

namespace FunctionField

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω]

/-- The constructed finite constant stages exhaust the actual maximal constant extension. -/
theorem iSup_fullConstantDegreeStage :
    (⨆ n : ℕ+, (fullConstantDegreeStage k K Ω (n : ℕ)).toIntermediateField) =
      IntermediateField.adjoin K
        (separableClosure (algebraicClosure k K) Ω : Set Ω) := by
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  apply le_antisymm
  · apply iSup_le
    intro n
    apply IntermediateField.adjoin.mono
    intro c hc
    rw [separableClosure_eq_iSup_finiteConstantsInClosure]
    exact (le_iSup (fun n : ℕ+ =>
      (finiteConstantsInClosure (algebraicClosure k K) Ω (n : ℕ)).toIntermediateField) n) hc
  · apply IntermediateField.adjoin_le_iff.mpr
    intro c hc
    have hle : separableClosure (algebraicClosure k K) Ω ≤
        (⨆ n : ℕ+, (fullConstantDegreeStage k K Ω (n : ℕ)).toIntermediateField).restrictScalars
          (algebraicClosure k K) := by
      rw [separableClosure_eq_iSup_finiteConstantsInClosure]
      apply iSup_le
      intro n x hx
      exact (le_iSup (fun n : ℕ+ =>
        (fullConstantDegreeStage k K Ω (n : ℕ)).toIntermediateField) n)
          (IntermediateField.subset_adjoin K _ hx)
    exact hle hc

variable [IsGalois K Ω]

/-- The concrete arithmetic inertia is the intersection of the fixing subgroups
of all actual finite constant extensions. -/
theorem fullConstantDegreeData_inertia_eq_iInf :
    (fullConstantDegreeData k K Ω).inertia.toSubgroup =
      ⨅ n : ℕ+, (fullConstantDegreeStage k K Ω (n : ℕ)).toIntermediateField.fixingSubgroup := by
  rw [fullConstantDegreeData_inertia, ← iSup_fullConstantDegreeStage]
  ext σ
  rw [Subgroup.mem_iInf]
  simp only [← Subgroup.zpowers_le,
    ← IntermediateField.le_iff_le, iSup_le_iff]

end FunctionField

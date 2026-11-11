/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.PrincipalRayKernel
public import Nyll.AlgebraicCurves.Places.Evaluation.Value
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnitTopology

/-!
# Full local principal units and the original place values

The actual completion principal-unit condition is equivalent to the function
having residue value one at the original place. This connects the boundary
coordinates of the principal ray kernel to the precise `HasValue u 1`
predicate used by Tamagawa's additive reconstruction.
-/

@[expose] public section

noncomputable section

open scoped ValuativeRel WithZero
open AlgebraicCurve

namespace FunctionField.RayClass

private theorem mem_fieldPrincipalUnits_one_of_sub_one_lt_one
    {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] [ValuativeRel F]
    (w : Valuation F Γ₀) [w.Compatible] (x : Fˣ) (hx : w ((x : F) - 1) < 1) :
    x ∈ LocalFieldTheory.fieldPrincipalUnits F 1 := by
  have hsmall : ValuativeRel.valuation F ((x : F) - 1) < 1 :=
    (ValuativeRel.isEquiv (ValuativeRel.valuation F) w).lt_one_iff_lt_one.mpr hx
  have hval : ValuativeRel.valuation F (x : F) = 1 := by
    have h := (ValuativeRel.valuation F).map_eq_of_sub_lt
      (show ValuativeRel.valuation F ((x : F) - 1) < ValuativeRel.valuation F 1 by
        rw [map_one]
        exact hsmall)
    exact h.trans (map_one (ValuativeRel.valuation F))
  obtain ⟨u, hu⟩ :=
    (LocalFieldTheory.mem_localBaseUnitSubgroup_iff_valuation_eq_one F x).mpr hval
  refine ⟨u, ?_, hu⟩
  apply (LocalFieldTheory.mem_principalUnits_iff F u 1).mpr
  rw [pow_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  apply (Valuation.Integer.not_isUnit_iff_valuation_lt_one
    (v := ValuativeRel.valuation F)).mpr
  change ValuativeRel.valuation F (((u : 𝒪[F]) : F) - 1) < 1
  have hcoe : ((u : 𝒪[F]) : F) = (x : F) := congrArg Units.val hu
  rw [hcoe]
  exact hsmall

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Full first principal units are characterized by the original completion valuation. -/
theorem localHigherUnitGroup_one_iff_sub_one_lt_one
    (v : Place k K) (x : v.adicCompletionˣ) :
    x ∈ localHigherUnitGroup v 1 ↔ Valued.v ((x : v.adicCompletion) - 1) < (1 : ℤᵐ⁰) := by
  constructor
  · exact localHigherUnit_sub_one_lt_one v (by decide) x
  · intro hx
    let : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
    have : (Valued.v : Valuation v.adicCompletion ℤᵐ⁰).Compatible :=
      Valuation.Compatible.ofValuation (Valued.v : Valuation v.adicCompletion ℤᵐ⁰)
    exact mem_fieldPrincipalUnits_one_of_sub_one_lt_one
      (Valued.v : Valuation v.adicCompletion ℤᵐ⁰) x hx

/-- Residue value one is exactly the original strict valuation condition on `x - 1`. -/
theorem hasValue_one_iff_adicValuation_sub_one_lt_one (v : Place k K) (x : K) :
    v.HasValue x 1 ↔ v.adicValuation (x - 1) < 1 := by
  constructor
  · intro hx
    have hmem : x - 1 ∈ v.toValuationSubring := sub_mem hx.mem (one_mem _)
    have hzero : IsLocalRing.residue v.toValuationSubring ⟨x - 1, hmem⟩ = 0 := by
      change IsLocalRing.residue v.toValuationSubring (⟨x, hx.mem⟩ - 1) = 0
      rw [map_sub, hx.residue_eq, map_one, map_one, sub_self]
    exact (v.mem_maximalIdeal_iff_adicValuation_lt_one ⟨x - 1, hmem⟩).mp
      ((IsLocalRing.residue_eq_zero_iff _).mp hzero)
  · intro hx
    have hmem : x - 1 ∈ v.toValuationSubring :=
      v.mem_iff_adicValuation_le_one.mpr hx.le
    have hmax := (v.mem_maximalIdeal_iff_adicValuation_lt_one ⟨x - 1, hmem⟩).mpr hx
    have hvalue : v.HasValue (x - 1) 0 :=
      ⟨hmem, ((IsLocalRing.residue_eq_zero_iff _).mpr hmax).trans (map_zero _).symm⟩
    simpa only [sub_add_cancel, zero_add] using hvalue.add v.hasValue_one

/-- The actual completion embedding identifies full principal units with the
original place's residue-value-one predicate. -/
theorem completion_mem_localHigherUnitGroup_one_iff_hasValue
    (v : Place k K) (x : Kˣ) :
    Units.map (algebraMap K v.adicCompletion) x ∈ localHigherUnitGroup v 1 ↔
      v.HasValue (x : K) 1 := by
  rw [localHigherUnitGroup_one_iff_sub_one_lt_one,
    hasValue_one_iff_adicValuation_sub_one_lt_one]
  change Valued.v (algebraMap K v.adicCompletion (x : K) - 1) < 1 ↔ _
  rw [← map_one (algebraMap K v.adicCompletion), ← map_sub,
    valued_algebraMap_adicCompletion]
  rfl

variable [HasPrincipalDivisors k K] [∀ v : Place k K, v.FiniteResidue]

/-- The actual principal kernel's reduced boundary coordinate detects precisely
the principal-unit predicate used by Tamagawa's lemma. -/
theorem rayLocalComponent_principalRayKernelEquiv_boundary_hasValue
    (m : Modulus k K) (hm : m ≠ 0) (v : Place k K) (hv : m v = 1) (x : Kˣ) :
    rayLocalComponent m v (principalRayKernelEquiv m hm x) = 1 ↔ v.HasValue (x : K) 1 :=
  (rayLocalComponent_principalRayKernelEquiv_boundary m hm v hv x).trans
    (completion_mem_localHigherUnitGroup_one_iff_hasValue v x)

end FunctionField.RayClass

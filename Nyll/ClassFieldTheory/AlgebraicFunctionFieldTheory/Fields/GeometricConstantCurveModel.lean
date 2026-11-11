/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.GeometricConstantExtension
public import Nyll.AlgebraicCurves.FunctionFields.Constants.ConstantSeparatingParameter
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveSeparatingTranscendental
public import Nyll.AlgebraicCurves.Models.Construction.BasicPerfectField
public import Nyll.SchemeTheory.Morphisms.GeometricallyIntegralAlgClosed
public import Mathlib.RingTheory.EssentialFiniteness

/-!
# A geometric curve model for the original constant compositum

The field is the same intermediate field used by the geometric Artin kernel.
An original separating parameter remains separating after its literal inclusion
into this compositum. This gives essential finite type and an actual proper
smooth model, including the original constant scalar map, function-field
equivalence, stalk images, and point/place bijection. Geometric integrality is
proved over the actual algebraically closed constant field.

No model or function-field comparison is supplied as an extra hypothesis.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve AlgebraicGeometry

namespace FunctionField

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]

local notation "C" => separableClosure k Ω
local notation "G" => geometricConstantExtension k K Ω

local instance geometricModelConstantsAlgebra : Algebra C G :=
  constantAlgebra (K := K) C

local instance geometricModelConstantsTower : IsScalarTower k C G :=
  constantScalarTower (K := K) C

/-- The geometric compositum has a separating parameter coming from the
original function field through the original inclusion. -/
theorem geometricConstantExtension_original_separatingParameter :
    ∃ t : K, Transcendental C (algebraMap K G t) ∧
      FiniteDimensional (IntermediateField.adjoin C ({algebraMap K G t} : Set G)) G ∧
      Algebra.IsSeparable (IntermediateField.adjoin C ({algebraMap K G t} : Set G)) G := by
  have hcurve : IsCurveOver k K := isCurveOver k K
  have hfinite : Algebra.EssFiniteType k K := essFiniteType k K
  obtain ⟨t, ht, hfin, hsep⟩ :=
    IsCurveOver.exists_separating_transcendental (K := k) (F := K)
  have htG : Transcendental k (algebraMap K G t) :=
    (transcendental_algebraMap_iff (algebraMap K G).injective).mpr ht
  obtain ⟨hfinG, hsepG⟩ := finite_separable_adjoin_constantBaseChange
    (K := k) (F := K) (K' := C) (F' := G) t
    (constantExtension_adjoin_originalField (K := K) C)
  exact ⟨t, htG.extendScalars C, hfinG, hsepG⟩

/-- Essential finite type is proved for the actual M1 function field with
its original constant inclusion. -/
theorem geometricConstantExtension_essFiniteType : Algebra.EssFiniteType C G := by
  obtain ⟨t, _, hfin, _⟩ :=
    geometricConstantExtension_original_separatingParameter k K Ω
  have hparameter :
      Algebra.EssFiniteType C (IntermediateField.adjoin C ({algebraMap K G t} : Set G)) :=
    IntermediateField.essFiniteType_iff.mpr
      ⟨{algebraMap K G t}, by rw [Finset.coe_singleton]⟩
  have hfinite :
      Algebra.EssFiniteType (IntermediateField.adjoin C ({algebraMap K G t} : Set G)) G :=
    inferInstance
  exact Algebra.EssFiniteType.comp C
    (IntermediateField.adjoin C ({algebraMap K G t} : Set G)) G

variable [IsSepClosed Ω]

local instance geometricModelConstantsAlgClosed : IsAlgClosed C :=
  IsAlgClosure.isAlgClosed (R := k) (K := C)

/-- A proper smooth model of the original geometric compositum. Its
`ffEquiv_algebraMap` and `range_stalk_eq` fields retain the specified constants
and the original geometric places. -/
def geometricConstantCurveModel : CurveModel C G := by
  let h := geometricConstantExtension_original_separatingParameter k K Ω
  let t : K := Classical.choose h
  have ht : Transcendental C (algebraMap K G t) := (Classical.choose_spec h).1
  have hfin :
      FiniteDimensional (IntermediateField.adjoin C ({algebraMap K G t} : Set G)) G :=
    (Classical.choose_spec h).2.1
  exact Classical.choice
    (CurveModel.nonempty_of_perfectField C G ⟨algebraMap K G t, ht, hfin⟩)

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- This actual model is geometrically integral over the same constant
field that acts on the original Artin-kernel function field. -/
theorem geometricConstantCurveModel_geometricallyIntegral :
    GeometricallyIntegral (geometricConstantCurveModel k K Ω).toBase :=
  geometricallyIntegral_of_isAlgClosed (geometricConstantCurveModel k K Ω).toBase

end FunctionField

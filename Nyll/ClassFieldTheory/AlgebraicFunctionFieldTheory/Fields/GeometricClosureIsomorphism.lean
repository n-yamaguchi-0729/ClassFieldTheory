/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricConstantArtinKernels
public import Nyll.GaloisCohomology.Topology.FieldIsomorphismClosure

/-!
# One ambient closure map for the original geometric reconstruction

The original ambient closures are also separable closures of their
geometric constant composita. Extending the geometric field isomorphism
once therefore retains its original-field and every finite-stage
coefficient formula. Native coordinates at a stage are obtained from
this single ambient map through the specified closure comparisons.
-/

@[expose] public section

noncomputable section

namespace FunctionField

open GaloisCohomology RayClass

universe uk u₁ v₁ u₂ v₂

variable (k : Type uk) (K₁ : Type u₁) (Ω₁ : Type v₁) (K₂ : Type u₂) (Ω₂ : Type v₂)
  [Field k] [Finite k] [Field K₁] [Field Ω₁] [Field K₂] [Field Ω₂]
  [Algebra k K₁] [Algebra (RatFunc k) K₁]
  [IsScalarTower k (RatFunc k) K₁] [FunctionField k K₁]
  [Algebra K₁ Ω₁] [IsSepClosure K₁ Ω₁] [IsSepClosed Ω₁]
  [Algebra k Ω₁] [IsScalarTower k K₁ Ω₁]
  [Algebra k K₂] [Algebra (RatFunc k) K₂]
  [IsScalarTower k (RatFunc k) K₂] [FunctionField k K₂]
  [Algebra K₂ Ω₂] [IsSepClosure K₂ Ω₂] [IsSepClosed Ω₂]
  [Algebra k Ω₂] [IsScalarTower k K₂ Ω₂]

local notation "G₁" => geometricConstantExtension k K₁ Ω₁
local notation "G₂" => geometricConstantExtension k K₂ Ω₂

/-- The first ambient closure remains a separable closure of its geometric field. -/
local instance firstGeometricClosure : IsSepClosure G₁ Ω₁ :=
  ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable K₁ G₁ Ω₁⟩
/-- The second ambient closure remains a separable closure of its geometric field. -/
local instance secondGeometricClosure : IsSepClosure G₂ Ω₂ :=
  ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable K₂ G₂ Ω₂⟩

variable (Φgeom : geometricConstantExtension k K₁ Ω₁ ≃+*
  geometricConstantExtension k K₂ Ω₂)

/-- A single extension of the actual geometric field map to the two
original supplied ambient closures. -/
def geometricFieldIsoClosureEquiv : Ω₁ ≃+* Ω₂ :=
  suppliedFieldIsoClosureEquiv (K := G₁) (F := G₂) Φgeom Ω₁ Ω₂

local notation "a" => geometricFieldIsoClosureEquiv k K₁ Ω₁ K₂ Ω₂ Φgeom

omit [Finite k] [Algebra k K₁] [Algebra (RatFunc k) K₁]
  [IsScalarTower k (RatFunc k) K₁] [FunctionField k K₁] [IsScalarTower k K₁ Ω₁]
  [Algebra k K₂] [Algebra (RatFunc k) K₂] [IsScalarTower k (RatFunc k) K₂]
  [FunctionField k K₂] [IsScalarTower k K₂ Ω₂] in
/-- Every geometric coefficient retains the original geometric map. -/
theorem geometricFieldIsoClosureEquiv_geometric (x : G₁) :
    a (algebraMap G₁ Ω₁ x) = algebraMap G₂ Ω₂ (Φgeom x) :=
  suppliedFieldIsoClosureEquiv_algebraMap (K := G₁) (F := G₂) Φgeom Ω₁ Ω₂ x

omit [Finite k] [Algebra k K₁] [Algebra (RatFunc k) K₁]
  [IsScalarTower k (RatFunc k) K₁] [FunctionField k K₁] [IsScalarTower k K₁ Ω₁]
  [Algebra k K₂] [Algebra (RatFunc k) K₂] [IsScalarTower k (RatFunc k) K₂]
  [FunctionField k K₂] [IsScalarTower k K₂ Ω₂] in
/-- The original-field coefficient formula follows from the retained
geometric coefficient formula and the original scalar towers. -/
theorem geometricFieldIsoClosureEquiv_base (Φ : K₁ ≃+* K₂)
    (hbase : ∀ x, Φgeom (algebraMap K₁ G₁ x) = algebraMap K₂ G₂ (Φ x)) (x : K₁) :
    a (algebraMap K₁ Ω₁ x) = algebraMap K₂ Ω₂ (Φ x) := by
  have h := geometricFieldIsoClosureEquiv_geometric k K₁ Ω₁ K₂ Ω₂ Φgeom
    (algebraMap K₁ G₁ x)
  rw [hbase, ← IsScalarTower.algebraMap_apply K₁ G₁ Ω₁,
    ← IsScalarTower.algebraMap_apply K₂ G₂ Ω₂] at h
  exact h

variable (n₁ n₂ : ℕ+)

local notation "L₁" =>
  FiniteGaloisIntermediateField.toIntermediateField (fullConstantDegreeStage k K₁ Ω₁ n₁)
local notation "L₂" =>
  FiniteGaloisIntermediateField.toIntermediateField (fullConstantDegreeStage k K₂ Ω₂ n₂)
local notation "i₁" => fullConstantStageGeometricInclusion k K₁ Ω₁ n₁
local notation "i₂" => fullConstantStageGeometricInclusion k K₂ Ω₂ n₂

/-- The first ambient closure is a separable closure of each original finite stage. -/
local instance firstStageClosure : IsSepClosure L₁ Ω₁ :=
  ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable K₁ L₁ Ω₁⟩
/-- The second ambient closure is a separable closure of each original finite stage. -/
local instance secondStageClosure : IsSepClosure L₂ Ω₂ :=
  ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable K₂ L₂ Ω₂⟩

/-- Every retained finite-stage formula is extended by this same
ambient map, with the original embedded field elements unchanged. -/
theorem geometricFieldIsoClosureEquiv_stage (Φi : L₁ ≃+* L₂)
    (hstage : ∀ x, Φgeom (i₁ x) = i₂ (Φi x)) (x : L₁) :
    a (algebraMap L₁ Ω₁ x) = algebraMap L₂ Ω₂ (Φi x) := by
  have h := geometricFieldIsoClosureEquiv_geometric k K₁ Ω₁ K₂ Ω₂ Φgeom (i₁ x)
  rw [hstage] at h
  change a (i₁ x : Ω₁) = (i₂ (Φi x) : Ω₂) at h
  rw [fullConstantStageGeometricInclusion_coe, fullConstantStageGeometricInclusion_coe] at h
  exact h

/-- The native coordinates of a finite stage use the single original
ambient extension, with no independently selected field extension. -/
def geometricFieldIsoNativeStageClosureEquiv : SeparableClosure L₁ ≃+* SeparableClosure L₂ :=
  nativeClosureEquivOfSupplied a
    (IsSepClosure.equiv L₁ (SeparableClosure L₁) Ω₁)
    (IsSepClosure.equiv L₂ (SeparableClosure L₂) Ω₂)

/-- The native stage map extends exactly the retained stage field map. -/
theorem geometricFieldIsoNativeStageClosureEquiv_algebraMap
    (Φi : L₁ ≃+* L₂) (hstage : ∀ x, Φgeom (i₁ x) = i₂ (Φi x)) (x : L₁) :
    geometricFieldIsoNativeStageClosureEquiv k K₁ Ω₁ K₂ Ω₂ Φgeom n₁ n₂
        (algebraMap L₁ (SeparableClosure L₁) x) =
      algebraMap L₂ (SeparableClosure L₂) (Φi x) :=
  nativeClosureEquivOfSupplied_algebraMap Φi a
    (IsSepClosure.equiv L₁ (SeparableClosure L₁) Ω₁)
    (IsSepClosure.equiv L₂ (SeparableClosure L₂) Ω₂)
    (geometricFieldIsoClosureEquiv_stage k K₁ Ω₁ K₂ Ω₂ Φgeom n₁ n₂ Φi hstage) x

end FunctionField

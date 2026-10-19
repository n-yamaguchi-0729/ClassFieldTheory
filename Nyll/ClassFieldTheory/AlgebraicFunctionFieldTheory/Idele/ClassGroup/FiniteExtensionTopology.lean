/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionFixed
import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# The discrete Galois module of actual idele classes

The finite-extension idele-class direct limit is given the discrete topology for
Galois cohomology. Each class is represented in a finite Galois extension, so its
stabilizer contains the open kernel of restriction to that finite stage. Hence
the actual ambient Krull Galois action is continuous. The finite-stage comparison
also agrees with the fixed subgroup used by the existing Herbrand framework.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup.FiniteExtensionLimit

open FiniteExtensionSystem
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable {k K Ω : Type*} [Field k] [PerfectField k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [FunctionField k K]

/-- The coefficient topology for Galois cohomology is discrete. -/
instance coefficientTopology : TopologicalSpace (Limit k K Ω) := ⊥

instance coefficientDiscreteTopology : DiscreteTopology (Limit k K Ω) := ⟨rfl⟩

/-- Restriction to an actual finite Galois stage has open kernel in the Krull topology. -/
theorem restrictionKernel_isOpen (E : FiniteGaloisIntermediateField K Ω) :
    IsOpen (((AlgEquiv.restrictNormalHom E : (Ω ≃ₐ[K] Ω) →* (E ≃ₐ[K] E)).ker) :
      Set (Ω ≃ₐ[K] Ω)) := by
  exact (isOpen_discrete ({1} : Set (E ≃ₐ[K] E))).preimage
    (InfiniteGalois.restrictNormalHom_continuous (E : IntermediateField K Ω))

/-- A finite-stage representative is fixed by the kernel of its field restriction. -/
theorem restrictionKernel_le_stabilizer (E : FiniteGaloisIntermediateField K Ω)
    (c : stage (k := k) E) :
    (AlgEquiv.restrictNormalHom E : (Ω ≃ₐ[K] Ω) →* (E ≃ₐ[K] E)).ker ≤
      MulAction.stabilizer (Ω ≃ₐ[K] Ω) (of (k := k) (K := K) (Ω := Ω) E c) := by
  intro σ hσ
  exact of_fixed_over_stage (k := k) (K := K) (Ω := Ω) E c σ hσ

/-- Every actual limit class has an open stabilizer. -/
theorem ambient_stabilizer_isOpen (c : Limit k K Ω) :
    IsOpen (MulAction.stabilizer (Ω ≃ₐ[K] Ω) c : Set (Ω ≃ₐ[K] Ω)) := by
  obtain ⟨E, a, rfl⟩ := exists_of (k := k) (K := K) (Ω := Ω) c
  exact Subgroup.isOpen_mono (restrictionKernel_le_stabilizer E a) (restrictionKernel_isOpen E)

/-- The ambient Krull Galois group acts continuously on the discrete actual
idele-class direct limit. -/
instance ambientContinuousSMul : ContinuousSMul (Ω ≃ₐ[K] Ω) (Limit k K Ω) :=
  continuousSMul_iff_stabilizer_isOpen.mpr ambient_stabilizer_isOpen

/-- The actual fixed subgroup is the subgroup used by the existing Herbrand API. -/
theorem fixedOverStage_eq_herbrandFixed (E : FiniteGaloisIntermediateField K Ω) :
    fixedOverStage (k := k) (K := K) (Ω := Ω) E =
      fixedSubgroup
        (AlgEquiv.restrictNormalHom E : (Ω ≃ₐ[K] Ω) →* (E ≃ₐ[K] E)).ker
        (Limit k K Ω) := by
  apply Subgroup.ext
  intro c
  rfl

variable [Normal K Ω]

/-- The concrete finite idele class group is the corresponding Herbrand fixed part. -/
def stageEquivHerbrandFixed (E : FiniteGaloisIntermediateField K Ω) :
    stage (k := k) E ≃*
      fixedSubgroup
        (AlgEquiv.restrictNormalHom E : (Ω ≃ₐ[K] Ω) →* (E ≃ₐ[K] E)).ker
        (Limit k K Ω) :=
  (stageEquivFixed (k := k) (K := K) (Ω := Ω) E).trans
    (MulEquiv.subgroupCongr (fixedOverStage_eq_herbrandFixed E))

/-- The Herbrand fixed-part comparison is the original finite-stage inclusion. -/
@[simp]
theorem coe_stageEquivHerbrandFixed (E : FiniteGaloisIntermediateField K Ω)
    (c : stage (k := k) E) :
    (stageEquivHerbrandFixed (k := k) (K := K) (Ω := Ω) E c : Limit k K Ω) =
      of (k := k) (K := K) (Ω := Ω) E c :=
  rfl

end FunctionField.IdeleClassGroup.FiniteExtensionLimit

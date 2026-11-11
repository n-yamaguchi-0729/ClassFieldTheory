/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.ConstantNorm
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.LiftedLocalUnitsH2

/-!
# The local-global kernel of constant-extension unit H²

Local vanishing gives a principal idele norm. The proved Hasse norm theorem
for the actual finite constant extension makes its representing unit a global
field norm, so its actual H² class is zero.
-/

@[expose] public section

universe u v w

noncomputable section

open AlgebraicCurve

namespace FunctionField

open ClassFieldTower.Cohomology

variable (k : Type u) (K : Type v) (Ω : Type w) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω] [IsSepClosed Ω]

/-- A unit H² class for an actual finite constant extension is detected by its completions. -/
theorem liftedConstantUnitsH2_eq_zero_of_forall_completion
    (n : ℕ) [NeZero n]
    (c : groupCohomology (liftedGaloisUnitsRep K (fullConstantDegreeStage k K Ω n)) 2)
    (hc : ∀ w : Place k (fullConstantDegreeStage k K Ω n),
      IdeleGroup.liftedCompletionUnitsH2Map (K := K) w c = 0) : c = 0 := by
  let C := fullConstantDegreeStage k K Ω n
  have hcyc : IsCyclic Gal(C/K) := isCyclic_fullConstantDegreeStage k K Ω n
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(C/K))
  obtain ⟨a, rfl⟩ := liftedCyclicBaseUnitH2Class_surjective K C g hg c
  have hprincipal := (IdeleGroup.liftedBaseUnitH2Class_locally_zero_iff_principal_norm
    (k := k) g hg a).mp hc
  have hpr : a ∈ NormObstruction.principalNormSubgroup (k := k) (K := K) (L := C) :=
    hprincipal
  have hfield :=
    (IdeleClassGroup.principalNormSubgroup_eq_fieldNormSubgroup_fullConstantDegreeStage
      k K Ω n).le hpr
  obtain ⟨x, hx⟩ := hfield
  exact (liftedCyclicBaseUnitH2Class_eq_zero_iff_norm K C g hg a).mpr
    ⟨(x : C), congrArg Units.val hx⟩

end FunctionField

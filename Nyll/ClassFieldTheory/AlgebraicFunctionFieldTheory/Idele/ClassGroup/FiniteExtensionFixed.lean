/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionAction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionLimit
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.FixedIdeles
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Galois fixed points of the actual idele-class direct limit

The compatible actions on the finite stages induce an action on their direct
limit. When the ambient extension is normal, restriction of automorphisms is
surjective. Injectivity of the finite-stage embeddings then reduces fixed-point
descent to the proved finite Galois descent of actual idele classes.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup.FiniteExtensionLimit

open FiniteExtensionSystem

variable {k K Ω : Type*} [Field k] [PerfectField k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω]
    [IsScalarTower (RatFunc k) K Ω] [IsScalarTower k (RatFunc k) Ω]
    [FunctionField k K]

private def stageActionToLimit (σ : Ω ≃ₐ[K] Ω) (E : FiniteGaloisIntermediateField K Ω) :
    stage (k := k) E →* Limit k K Ω :=
  (of (k := k) (K := K) (Ω := Ω) E).comp
    (MulDistribMulAction.toMonoidHom (stage (k := k) E) σ)

private theorem stageActionToLimit_transition (σ : Ω ≃ₐ[K] Ω)
    (E F : FiniteGaloisIntermediateField K Ω) (h : E ≤ F) (c : stage (k := k) E) :
    stageActionToLimit (k := k) (K := K) (Ω := Ω) σ F
        (transition (k := k) E F h c) =
      stageActionToLimit (k := k) (K := K) (Ω := Ω) σ E c :=
  (congrArg (of (k := k) (K := K) (Ω := Ω) F)
    (transition_smul (k := k) E F h σ c).symm).trans
      (of_transition (k := k) (K := K) (Ω := Ω) E F h (σ • c))

/-- An ambient automorphism acts on the direct limit through its compatible
actions on the actual finite-stage idele class groups. -/
def actionHom (σ : Ω ≃ₐ[K] Ω) : Limit k K Ω →* Limit k K Ω :=
  lift (k := k) (K := K) (Ω := Ω) (A := Limit k K Ω)
    (fun E : FiniteGaloisIntermediateField K Ω =>
      stageActionToLimit (k := k) (K := K) (Ω := Ω) σ E)
    (stageActionToLimit_transition (k := k) (K := K) (Ω := Ω) σ)

/-- The induced automorphism is computed by the actual action on a representative. -/
@[simp]
theorem actionHom_of (σ : Ω ≃ₐ[K] Ω) (E : FiniteGaloisIntermediateField K Ω)
    (c : stage (k := k) E) :
    actionHom (k := k) (K := K) (Ω := Ω) σ
        (of (k := k) (K := K) (Ω := Ω) E c) =
      of (k := k) (K := K) (Ω := Ω) E (σ • c) :=
  rfl

private theorem actionHom_one_apply (c : Limit k K Ω) :
    actionHom (k := k) (K := K) (Ω := Ω) 1 c = c := by
  obtain ⟨E, a, rfl⟩ := exists_of (k := k) (K := K) (Ω := Ω) c
  exact (actionHom_of (k := k) (K := K) (Ω := Ω) 1 E a).trans
    (congrArg (of (k := k) (K := K) (Ω := Ω) E) (one_smul (Ω ≃ₐ[K] Ω) a))

private theorem actionHom_mul_apply (σ τ : Ω ≃ₐ[K] Ω) (c : Limit k K Ω) :
    actionHom (k := k) (K := K) (Ω := Ω) (σ * τ) c =
      actionHom (k := k) (K := K) (Ω := Ω) σ
        (actionHom (k := k) (K := K) (Ω := Ω) τ c) := by
  obtain ⟨E, a, rfl⟩ := exists_of (k := k) (K := K) (Ω := Ω) c
  calc
    actionHom (k := k) (K := K) (Ω := Ω) (σ * τ)
        (of (k := k) (K := K) (Ω := Ω) E a) =
        of (k := k) (K := K) (Ω := Ω) E ((σ * τ) • a) :=
      actionHom_of (k := k) (K := K) (Ω := Ω) (σ * τ) E a
    _ = of (k := k) (K := K) (Ω := Ω) E (σ • (τ • a)) :=
      congrArg (of (k := k) (K := K) (Ω := Ω) E) (mul_smul σ τ a)
    _ = actionHom (k := k) (K := K) (Ω := Ω) σ
        (of (k := k) (K := K) (Ω := Ω) E (τ • a)) :=
      (actionHom_of (k := k) (K := K) (Ω := Ω) σ E (τ • a)).symm
    _ = actionHom (k := k) (K := K) (Ω := Ω) σ
        (actionHom (k := k) (K := K) (Ω := Ω) τ
          (of (k := k) (K := K) (Ω := Ω) E a)) :=
      congrArg (actionHom (k := k) (K := K) (Ω := Ω) σ)
        (actionHom_of (k := k) (K := K) (Ω := Ω) τ E a).symm

/-- The relative Galois group of the ambient extension acts multiplicatively
on the actual finite-extension idele-class direct limit. -/
instance ambientAction : MulDistribMulAction (Ω ≃ₐ[K] Ω) (Limit k K Ω) where
  smul σ c := actionHom (k := k) (K := K) (Ω := Ω) σ c
  one_smul := actionHom_one_apply (k := k) (K := K) (Ω := Ω)
  mul_smul := actionHom_mul_apply (k := k) (K := K) (Ω := Ω)
  smul_one σ := (actionHom (k := k) (K := K) (Ω := Ω) σ).map_one
  smul_mul σ c d := (actionHom (k := k) (K := K) (Ω := Ω) σ).map_mul c d

/-- The scalar operation is exposed directly so that heterogeneous scalar
notation does not search through unrelated quotient scalar structures. -/
instance ambientSMul : SMul (Ω ≃ₐ[K] Ω) (Limit k K Ω) where
  smul σ c := actionHom (k := k) (K := K) (Ω := Ω) σ c

/-- Expose the compatible group action directly for stabilizer and continuity APIs. -/
instance ambientMulAction : MulAction (Ω ≃ₐ[K] Ω) (Limit k K Ω) :=
  (ambientAction (k := k) (K := K) (Ω := Ω)).toMulAction

/-- Inclusion of a finite stage intertwines the ambient Galois actions. -/
@[simp]
theorem smul_of (σ : Ω ≃ₐ[K] Ω) (E : FiniteGaloisIntermediateField K Ω)
    (c : stage (k := k) E) :
    σ • of (k := k) (K := K) (Ω := Ω) E c =
      of (k := k) (K := K) (Ω := Ω) E (σ • c) :=
  rfl

/-- Injectivity of a finite-stage map reflects fixedness of its representative. -/
theorem of_fixed_iff (σ : Ω ≃ₐ[K] Ω) (E : FiniteGaloisIntermediateField K Ω)
    (c : stage (k := k) E) :
    σ • of (k := k) (K := K) (Ω := Ω) E c =
      of (k := k) (K := K) (Ω := Ω) E c ↔ σ • c = c := by
  rw [smul_of, (of_injective (k := k) (K := K) (Ω := Ω) E).eq_iff]

/-- The fixed subgroup for the actual kernel of restriction to a finite stage. -/
def fixedOverStage (E : FiniteGaloisIntermediateField K Ω) : Subgroup (Limit k K Ω) :=
  FixedPoints.subgroup (AlgEquiv.restrictNormalHom E : (Ω ≃ₐ[K] Ω) →* (E ≃ₐ[K] E)).ker
    (Limit k K Ω)

/-- Being fixed over a stage means being fixed by every ambient automorphism
whose actual restriction to that field is the identity. -/
theorem mem_fixedOverStage_iff (E : FiniteGaloisIntermediateField K Ω) (z : Limit k K Ω) :
    z ∈ fixedOverStage (k := k) (K := K) (Ω := Ω) E ↔
      ∀ σ : Ω ≃ₐ[K] Ω, AlgEquiv.restrictNormalHom E σ = 1 → σ • z = z := by
  constructor
  · intro hz σ hσ
    exact hz ⟨σ, hσ⟩
  · intro hz σ
    exact hz σ.1 σ.2

variable [Normal K Ω]

/-- Every automorphism of a finite Galois stage is seen by the actual ambient action. -/
theorem fixed_representative_of_fixed (E : FiniteGaloisIntermediateField K Ω)
    (c : stage (k := k) E)
    (hc : ∀ σ : Ω ≃ₐ[K] Ω, σ • of (k := k) (K := K) (Ω := Ω) E c =
      of (k := k) (K := K) (Ω := Ω) E c) :
    ∀ τ : E ≃ₐ[K] E, AlgebraicCurve.SemilinearAut.ofAlgAut (τ.restrictScalars k) • c = c := by
  intro τ
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) (E := Ω) τ
  have h := (of_fixed_iff (k := k) (K := K) (Ω := Ω) σ E c).1 (hc σ)
  rw [stage_smul_eq_restrict, hσ] at h
  exact h

omit [Normal K Ω] in
/-- A stage embeds into the classes fixed by every ambient automorphism
whose restriction to that stage is trivial. -/
theorem of_fixed_over_stage (E : FiniteGaloisIntermediateField K Ω)
    (c : stage (k := k) E) (σ : Ω ≃ₐ[K] Ω)
    (hσ : AlgEquiv.restrictNormalHom E σ = 1) :
    σ • of (k := k) (K := K) (Ω := Ω) E c =
      of (k := k) (K := K) (Ω := Ω) E c := by
  rw [smul_of, stage_smul_eq_restrict, hσ, one_smul]

/-- Automorphisms of a larger finite stage over a smaller one lift to ambient
automorphisms that fix the smaller stage pointwise. -/
theorem exists_lift_fixing_stage {E H : FiniteGaloisIntermediateField K Ω} (h : E ≤ H) :
    let _ : Algebra E H := inclusionAlgebra h
    let _ : IsScalarTower K E H := inclusion_baseScalarTower h
    ∀ η : H ≃ₐ[E] H, ∃ σ : Ω ≃ₐ[K] Ω,
      AlgEquiv.restrictNormalHom H σ = η.restrictScalars K ∧
        AlgEquiv.restrictNormalHom E σ = 1 := by
  intro aEH ht η
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := K) (K₁ := H) (E := Ω) (η.restrictScalars K)
  refine ⟨σ, hσ, ?_⟩
  apply AlgEquiv.ext
  intro x
  apply (algebraMap E Ω).injective
  change algebraMap E Ω ((AlgEquiv.restrictNormalHom E σ) x) = algebraMap E Ω x
  calc
    algebraMap E Ω ((AlgEquiv.restrictNormalHom E σ) x) = σ (algebraMap E Ω x) :=
      AlgEquiv.restrictNormal_commutes σ E x
    _ = algebraMap H Ω ((AlgEquiv.restrictNormalHom H σ) (algebraMap E H x)) :=
      (AlgEquiv.restrictNormal_commutes σ H (algebraMap E H x)).symm
    _ = algebraMap H Ω (η (algebraMap E H x)) :=
      congrArg (algebraMap H Ω) (DFunLike.congr_fun hσ (algebraMap E H x))
    _ = algebraMap E Ω x := congrArg (algebraMap H Ω) (η.commutes x)

/-- A limit class fixed pointwise over a finite Galois stage is represented
by an actual idele class of that stage. -/
theorem exists_of_of_fixed_over_stage (E : FiniteGaloisIntermediateField K Ω)
    (z : Limit k K Ω)
    (hz : ∀ σ : Ω ≃ₐ[K] Ω, AlgEquiv.restrictNormalHom E σ = 1 → σ • z = z) :
    ∃ c : stage (k := k) E, of (k := k) (K := K) (Ω := Ω) E c = z := by
  obtain ⟨F, c, hc⟩ := exists_of (k := k) (K := K) (Ω := Ω) z
  let H : FiniteGaloisIntermediateField K Ω := E ⊔ F
  let aEH : Algebra E H := inclusionAlgebra (show E ≤ H from le_sup_left)
  have : IsScalarTower K E H := inclusion_baseScalarTower (show E ≤ H from le_sup_left)
  have : IsScalarTower k E H := inclusion_scalarTower (k := k) (show E ≤ H from le_sup_left)
  have : FiniteDimensional E H := inclusion_finiteDimensional (show E ≤ H from le_sup_left)
  have : IsGalois E H := inclusion_isGalois (show E ≤ H from le_sup_left)
  let d : stage (k := k) H := transition (k := k) F H (show F ≤ H from le_sup_right) c
  have hd : of (k := k) (K := K) (Ω := Ω) H d = z :=
    (of_transition (k := k) (K := K) (Ω := Ω) F H le_sup_right c).trans hc
  have hfixed : ∀ η : H ≃ₐ[E] H,
      AlgebraicCurve.SemilinearAut.ofAlgAut (η.restrictScalars k) • d = d := by
    intro η
    obtain ⟨σ, hσH, hσE⟩ := exists_lift_fixing_stage (show E ≤ H from le_sup_left) η
    have hfix := hz σ hσE
    rw [← hd] at hfix
    have hstage := (of_fixed_iff (k := k) (K := K) (Ω := Ω) σ H d).1 hfix
    rw [stage_smul_eq_restrict, hσH] at hstage
    exact hstage
  obtain ⟨b, hb⟩ := IdeleClassGroup.exists_baseChange_of_algAut_fixed d hfixed
  refine ⟨b, ?_⟩
  rw [← of_transition (k := k) (K := K) (Ω := Ω) E H (show E ≤ H from le_sup_left)]
  exact (congrArg (of (k := k) (K := K) (Ω := Ω) H) hb).trans hd

/-- The fixed part over a finite Galois intermediate field is precisely its
actual embedded idele class group. -/
theorem mem_range_of_iff_fixed_over_stage (E : FiniteGaloisIntermediateField K Ω)
    (z : Limit k K Ω) :
    z ∈ (of (k := k) (K := K) (Ω := Ω) E).range ↔
      ∀ σ : Ω ≃ₐ[K] Ω, AlgEquiv.restrictNormalHom E σ = 1 → σ • z = z := by
  constructor
  · rintro ⟨c, rfl⟩ σ hσ
    exact of_fixed_over_stage (k := k) (K := K) (Ω := Ω) E c σ hσ
  · exact exists_of_of_fixed_over_stage E z

/-- The actual finite-stage image equals the corresponding fixed subgroup. -/
theorem range_of_eq_fixedOverStage (E : FiniteGaloisIntermediateField K Ω) :
    (of (k := k) (K := K) (Ω := Ω) E).range = fixedOverStage (k := k) (K := K) (Ω := Ω) E := by
  apply Subgroup.ext
  intro z
  rw [mem_range_of_iff_fixed_over_stage, mem_fixedOverStage_iff]

/-- The actual idele class group at a finite Galois stage is its fixed part
inside the ambient idele-class direct limit. -/
def stageEquivFixed (E : FiniteGaloisIntermediateField K Ω) :
    stage (k := k) E ≃* fixedOverStage (k := k) (K := K) (Ω := Ω) E :=
  (MonoidHom.ofInjective (of_injective (k := k) (K := K) (Ω := Ω) E)).trans
    (MulEquiv.subgroupCongr (range_of_eq_fixedOverStage E))

/-- The fixed-part comparison uses the actual inclusion into the direct limit. -/
@[simp]
theorem coe_stageEquivFixed (E : FiniteGaloisIntermediateField K Ω)
    (c : stage (k := k) E) :
    (stageEquivFixed (k := k) (K := K) (Ω := Ω) E c : Limit k K Ω) =
      of (k := k) (K := K) (Ω := Ω) E c :=
  rfl

end FunctionField.IdeleClassGroup.FiniteExtensionLimit

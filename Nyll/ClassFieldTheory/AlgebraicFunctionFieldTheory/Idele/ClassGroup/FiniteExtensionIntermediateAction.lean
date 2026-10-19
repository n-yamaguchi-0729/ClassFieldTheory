/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionIntermediate
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeAction

/-!
# Equivariance for arbitrary finite intermediate idele classes

An ambient automorphism preserving a finite intermediate field acts on its
idele classes through the actual restricted field automorphism. The proof
passes through its finite normal closure and the completed base-change maps.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup.FiniteExtensionLimit

open FiniteExtensionSystem

variable {k K Ω : Type*} [Field k] [PerfectField k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [FunctionField k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω]

/-- Inclusion into a finite Galois stage respects compatible field automorphisms. -/
theorem includeInStage_algAut_smul (E : IntermediateField K Ω) [FiniteDimensional K E]
    (H : FiniteGaloisIntermediateField K Ω) (hEH : E ≤ H)
    (σ : Gal(Ω/K)) (τ : E ≃ₐ[k] E)
    (hστ : ∀ x : E, σ (x : Ω) = (τ x : Ω)) (c : IdeleClassGroup k E) :
    includeInStage (k := k) E H hEH (AlgebraicCurve.SemilinearAut.ofAlgAut τ • c) =
      σ • includeInStage (k := k) E H hEH c := by
  let aEH : Algebra E H := (IntermediateField.inclusion hEH).toRingHom.toAlgebra
  have hKEH : IsScalarTower K E H := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hkEH : IsScalarTower k E H := IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have hfin : FiniteDimensional E H := FiniteDimensional.right K E H
  have hgal : IsGalois E H := IsGalois.tower_top_of_isGalois K E H
  have hcomp : ∀ x : E, (AlgEquiv.restrictNormalHom H σ) (algebraMap E H x) =
      algebraMap E H (τ x) := by
    intro x
    apply Subtype.ext
    exact (AlgEquiv.restrictNormal_commutes σ H (algebraMap E H x)).trans (hστ x)
  exact IdeleClassGroup.baseChange_algAut_smul
    ((AlgEquiv.restrictNormalHom H σ).restrictScalars k) τ hcomp c

/-- Actual intermediate-field inclusion respects compatible ambient and field automorphisms. -/
theorem ofIntermediate_algAut_smul [IsGalois K Ω]
    (E : IntermediateField K Ω) [FiniteDimensional K E]
    (σ : Gal(Ω/K)) (τ : E ≃ₐ[k] E)
    (hστ : ∀ x : E, σ (x : Ω) = (τ x : Ω)) (c : IdeleClassGroup k E) :
    ofIntermediate (k := k) E (AlgebraicCurve.SemilinearAut.ofAlgAut τ • c) =
      σ • ofIntermediate (k := k) E c := by
  let H := normalClosureStage E
  have hEH : E ≤ H := IntermediateField.le_normalClosure E
  calc
    ofIntermediate (k := k) E (AlgebraicCurve.SemilinearAut.ofAlgAut τ • c) =
        of (k := k) H (includeInStage (k := k) E H hEH
          (AlgebraicCurve.SemilinearAut.ofAlgAut τ • c)) := ofIntermediate_eq_of E H hEH _
    _ = of (k := k) H (σ • includeInStage (k := k) E H hEH c) :=
      congrArg (of (k := k) H) (includeInStage_algAut_smul E H hEH σ τ hστ c)
    _ = σ • of (k := k) H (includeInStage (k := k) E H hEH c) :=
      (smul_of σ H _).symm
    _ = σ • ofIntermediate (k := k) E c :=
      congrArg (fun z : Limit k K Ω => σ • z) (ofIntermediate_eq_of E H hEH c).symm

end FunctionField.IdeleClassGroup.FiniteExtensionLimit

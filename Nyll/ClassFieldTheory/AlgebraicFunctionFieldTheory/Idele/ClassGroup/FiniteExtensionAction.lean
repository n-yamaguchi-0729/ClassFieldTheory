/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionSystem
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeAction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.GaloisAction

/-!
# Ambient Galois action on finite idele-class stages

Each finite Galois intermediate field is preserved by every automorphism of the
ambient extension. Restriction therefore acts on its actual idele class group.
The completed base-change naturality theorem proves that every transition map
intertwines these actions.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup.FiniteExtensionSystem

variable {k K Ω : Type*} [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω]
    [FunctionField k K] [PerfectField k]

/-- Ambient automorphisms act on a finite stage by restriction to its actual field. -/
instance stageAmbientAction (E : FiniteGaloisIntermediateField K Ω) :
    MulDistribMulAction (Ω ≃ₐ[K] Ω) (stage (k := k) E) :=
  MulDistribMulAction.compHom (stage (k := k) E) (AlgEquiv.restrictNormalHom E)

/-- The ambient action on a stage is the completed action of the restricted automorphism. -/
theorem stage_smul_eq_restrict (E : FiniteGaloisIntermediateField K Ω)
    (σ : Ω ≃ₐ[K] Ω) (c : stage (k := k) E) :
    σ • c = (AlgEquiv.restrictNormalHom E σ) • c :=
  rfl

/-- Restricted ambient automorphisms commute with actual intermediate-field inclusions. -/
theorem restrictNormal_compatible {E F : FiniteGaloisIntermediateField K Ω}
    (h : E ≤ F) (σ : Ω ≃ₐ[K] Ω) :
    let _ : Algebra E F := inclusionAlgebra h
    ∀ x : E, (AlgEquiv.restrictNormalHom F σ) (algebraMap E F x) =
      algebraMap E F ((AlgEquiv.restrictNormalHom E σ) x) := by
  intro aEF x
  apply Subtype.ext
  change algebraMap F Ω ((AlgEquiv.restrictNormalHom F σ) (algebraMap E F x)) =
    algebraMap E Ω ((AlgEquiv.restrictNormalHom E σ) x)
  exact (AlgEquiv.restrictNormal_commutes σ F (algebraMap E F x)).trans
    (AlgEquiv.restrictNormal_commutes σ E x).symm

/-- The actual transition maps are equivariant for the ambient Galois action. -/
theorem transition_smul (E F : FiniteGaloisIntermediateField K Ω) (h : E ≤ F)
    (σ : Ω ≃ₐ[K] Ω) (c : stage (k := k) E) :
    transition (k := k) E F h (σ • c) = σ • transition (k := k) E F h c := by
  let aEF : Algebra E F := inclusionAlgebra h
  have : IsScalarTower k E F := inclusion_scalarTower (k := k) h
  have : FiniteDimensional E F := inclusion_finiteDimensional h
  have : IsGalois E F := inclusion_isGalois h
  exact IdeleClassGroup.baseChange_algAut_smul
    ((AlgEquiv.restrictNormalHom F σ).restrictScalars k)
    ((AlgEquiv.restrictNormalHom E σ).restrictScalars k)
    (restrictNormal_compatible h σ) c

end FunctionField.IdeleClassGroup.FiniteExtensionSystem

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# The actual cyclic Galois group of a compositum

The given intermediate field embeds into its compositum by inclusion.
Restriction of relative automorphisms to that field is injective, so cyclicity
is inherited from the original extension.
-/

noncomputable section

namespace FieldTheory

open IntermediateField

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- The actual inclusion of a field in the compositum formed over the other field. -/
def compositumEmbedding (L C : IntermediateField K Ω) :
    L →ₐ[K] adjoin C (L : Set Ω) :=
  inclusion (show L ≤ (adjoin C (L : Set Ω)).restrictScalars K from subset_adjoin C _)

/-- The given original-field action agrees with the inclusion into the compositum. -/
theorem compositumScalarTower (L C : IntermediateField K Ω) :
    let _ : Algebra L (adjoin C (L : Set Ω)) := (compositumEmbedding L C).toAlgebra
    IsScalarTower K L (adjoin C (L : Set Ω)) := by
  intro algL
  exact IsScalarTower.of_algebraMap_eq (fun x => ((compositumEmbedding L C).commutes x).symm)

/-- Finite Galois intermediate fields have a finite Galois compositum. -/
theorem finiteGalois_adjoin_intermediateField (L C : IntermediateField K Ω)
    [FiniteDimensional K L] [FiniteDimensional K C] [IsGalois K L] [IsGalois K C] :
    FiniteDimensional K (adjoin C (L : Set Ω)) ∧ IsGalois K (adjoin C (L : Set Ω)) := by
  have heq : (adjoin C (L : Set Ω)).restrictScalars K = C ⊔ L := by
    rw [restrictScalars_adjoin_eq_sup, adjoin_self]
  let e : adjoin C (L : Set Ω) ≃ₐ[K] (C ⊔ L : IntermediateField K Ω) := equivOfEq heq
  exact ⟨e.symm.toLinearEquiv.finiteDimensional, IsGalois.of_algEquiv e.symm⟩

/-- A cyclic extension stays cyclic after adjoining an arbitrary intermediate field. -/
theorem isCyclic_adjoin_intermediateField (L C : IntermediateField K Ω)
    [Normal K L] [IsCyclic Gal(L/K)] :
    IsCyclic Gal((adjoin C (L : Set Ω))/C) := by
  let N := adjoin C (L : Set Ω)
  let : Algebra L N := (compositumEmbedding L C).toAlgebra
  have : IsScalarTower K L N := compositumScalarTower L C
  let r : Gal(N/C) →* Gal(L/K) :=
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L).comp (AlgEquiv.restrictScalarsHom K)
  apply isCyclic_of_injective r
  intro σ τ hστ
  have heq : σ.toAlgHom = τ.toAlgHom := by
    apply adjoin_algHom_ext C
    intro x hx
    let y : L := ⟨x, hx⟩
    have hr := congrArg (fun η : Gal(L/K) => algebraMap L N (η y)) hστ
    exact ((σ.restrictScalars K).restrictNormal_commutes L y).symm.trans
      (hr.trans ((τ.restrictScalars K).restrictNormal_commutes L y))
  exact AlgEquiv.ext (fun x => AlgHom.congr_fun heq x)

end FieldTheory

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormGalois
import Nyll.AlgebraicCurves.Places.Restriction.AlgEquivSmulEqRestrictEq

/-!
# Local norm images in a Galois fiber

Conjugacy identifies the norm images at all places over one base place.
Consequently the corresponding component of an idele norm is a norm at
each chosen upper place, even though its definition is a product over the fiber.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField.IdeleGroup

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Conjugate actual places have the same local norm image over the specified base place. -/
theorem localNormOver_range_eq (v : Place k K) (w u : Place k L)
    (hw : w.restrict K = v) (hu : u.restrict K = v) :
    (localNormOver v w hw).range = (localNormOver v u hu).range := by
  have hle (w u : Place k L) (hw : w.restrict K = v) (hu : u.restrict K = v) :
      (localNormOver v w hw).range ≤ (localNormOver v u hu).range := by
    obtain ⟨σ, rfl⟩ := Place.exists_algEquiv_smul_eq_of_restrict_eq w u (hu.trans hw.symm)
    rintro y ⟨x, rfl⟩
    exact ⟨placeCompletionUnitsEquiv (SemilinearAut.ofAlgAut (σ.restrictScalars k)) w x,
      localNormOver_algAut σ v w hw x⟩
  exact le_antisymm (hle w u hw hu) (hle u w hu hw)

/-- The component of an actual idele norm is a norm at any specified place in its fiber. -/
theorem norm_component_mem_localNorm_range (w : Place k L) (b : IdeleGroup k L) :
    (norm (k := k) (K := K) (L := L) b) (w.restrict K) ∈
      (localNorm (K := K) w).range := by
  classical
  change normComponent (K := K) (L := L) (w.restrict K) b ∈
    (localNorm (K := K) w).range
  rw [normComponent_apply]
  apply Subgroup.prod_mem
  intro u _
  have hr := localNormOver_range_eq (w.restrict K) u.1 w
    ((Place.mem_fiberOver (w.restrict K)).mp u.2) rfl
  exact hr ▸ (show localNormOver (w.restrict K) u.1
    ((Place.mem_fiberOver (w.restrict K)).mp u.2) (b u.1) ∈
      (localNormOver (w.restrict K) u.1 ((Place.mem_fiberOver (w.restrict K)).mp u.2)).range
    from ⟨b u.1, rfl⟩)

variable [HasPrincipalDivisors k K]

/-- A principal idele norm supplies an actual norm preimage at every completed place. -/
theorem exists_localNorm_preimage_of_principal_norm
    (a : Kˣ) (b : IdeleGroup k L)
    (hb : norm (k := k) (K := K) (L := L) b = principalIdele k K a) (w : Place k L) :
    ∃ x : w.adicCompletionˣ,
      localNorm (K := K) w x = Units.map (algebraMap K (w.restrict K).adicCompletion) a := by
  have h := norm_component_mem_localNorm_range (K := K) (L := L) w b
  rw [hb] at h
  exact h

end FunctionField.IdeleGroup

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Finiteness
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.UnramifiedFrobenius
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.DecompositionResidueRestriction
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChangeTower

/-!
# Arithmetic Frobenius under arbitrary finite base change

The restriction formula uses the original residue-field action and the
actual residue degree of the base extension. The base extension may be
inseparable and the common upper field need not be normal over the bottom.
-/

noncomputable section
open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField

open AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg_exchange.BifibreW2

variable {k K F L M : Type} [Field k] [Finite k]
    [Field K] [Field F] [Field L] [Field M]
    [Algebra k K] [Algebra k F] [Algebra k L] [Algebra k M]
    [Algebra K F] [Algebra K L] [Algebra K M] [Algebra F M] [Algebra L M]
    [IsScalarTower k K F] [IsScalarTower k K L] [IsScalarTower k K M]
    [IsScalarTower k F M] [IsScalarTower k L M]
    [IsScalarTower K F M] [IsScalarTower K L M]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    [Algebra (RatFunc k) M] [IsScalarTower k (RatFunc k) M] [FunctionField k M]
    [FiniteDimensional K F]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [FiniteDimensional F M] [IsAbelianGalois F M]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k F]
    [HasPrincipalDivisors k L] [HasPrincipalDivisors k M]

/-- In a compatible finite square, upper arithmetic Frobenius restricts
to lower arithmetic Frobenius raised to the base residue degree. -/
theorem unramifiedDecompositionFrobenius_restrictNormal (u : Place k M) :
    let _ : FiniteDimensional K M := FiniteDimensional.trans K F M
    let _ : FiniteDimensional L M := FiniteDimensional.right K L M
    ∀ (hu : u.ramificationIndex F = 1) (hz : (u.restrict L).ramificationIndex K = 1),
      AlgEquiv.restrictNormalHom L
        ((unramifiedDecompositionFrobenius (K := F) u hu).val.restrictScalars K) =
      (unramifiedDecompositionFrobenius (K := K) (u.restrict L) hz).val ^
        (u.restrict F).inertiaDeg K := by
  intro hKMfinite hLMfinite hu hz
  let w : Place k F := u.restrict F
  let z : Place k L := u.restrict L
  let v : Place k K := z.restrict K
  have hw : w.restrict K = v :=
    (restrict_restrict (F := K) (E := F) u).trans
      (restrict_restrict (F := K) (E := L) u).symm
  let τ : IdeleGroup.decompositionGroup (K := F) u :=
    unramifiedDecompositionFrobenius (K := F) u hu
  let τK : IdeleGroup.decompositionGroup (K := K) u :=
    ⟨τ.val.restrictScalars K, τ.property⟩
  let σ : IdeleGroup.decompositionGroup (K := K) z :=
    ⟨AlgEquiv.restrictNormalHom L τK.val,
      IdeleGroup.restrictNormal_mem_decompositionGroup u τK⟩
  have hresidueFinite : Finite w.ResidueField := finite_residueField k F w
  have hresfinite : Module.Finite (w.restrict K).ResidueField w.ResidueField :=
    Module.Finite.of_finite
  have hcard : Nat.card w.ResidueField =
      Nat.card v.ResidueField ^ w.inertiaDeg K := by
    have h := Module.natCard_eq_pow_finrank
      (K := (w.restrict K).ResidueField) (V := w.ResidueField)
    change Nat.card w.ResidueField =
      Nat.card (w.restrict K).ResidueField ^ w.inertiaDeg K at h
    rw [hw] at h
    exact h
  have hτ (y : u.ResidueField) :
      IdeleGroup.decompositionResidueAut (K := K) u τK y =
        y ^ Nat.card w.ResidueField :=
    unramifiedDecompositionFrobenius_residue (K := F) u hu y
  have hres : IdeleGroup.decompositionResidueAut (K := K) z σ =
      IdeleGroup.decompositionResidueAut (K := K) z
        (unramifiedDecompositionFrobenius (K := K) z hz ^ w.inertiaDeg K) := by
    apply AlgEquiv.ext
    intro y
    apply (u.restrictResidueMap L).injective
    rw [IdeleGroup.decompositionResidueAut_restrictNormal u τK σ rfl,
      hτ, unramifiedDecompositionFrobenius_pow_residue, map_pow, hcard]
  have hσ := (decompositionResidueAut_bijective_of_ramificationIndex_eq_one z hz).1 hres
  exact congrArg Subtype.val hσ

end FunctionField

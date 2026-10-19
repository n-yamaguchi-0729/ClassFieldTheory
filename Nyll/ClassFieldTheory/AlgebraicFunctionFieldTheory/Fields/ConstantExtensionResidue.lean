/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Residue.ConstantResidueDegree
import Nyll.AlgebraicCurves.Places.Ramification.CardFiberOverMulRamificationIndexMulInertiaDeg
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionUnramified
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FullConstants

/-!
# Residue degrees and splitting in the actual constant tower

The residue degree formulas for a generated constant compositum apply to the
actual intermediate fields constructed here. For the degree-`n` extension of
the full constants, a place of degree `d` has residue extension degree
`n / gcd(n,d)` and splits into exactly `gcd(n,d)` places.
-/

noncomputable section

namespace FunctionField

open AlgebraicCurve

variable {k K Ω : Type*} [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [Finite k] (C : IntermediateField k Ω) [FiniteDimensional k C] [IsCurveOver k K]

/-- The degree of a residue field in the actual constant compositum. -/
theorem deg_constantExtension (w : Place k (constantExtensionStage (K := K) C)) :
    w.deg = Nat.lcm (Module.finrank k C) (w.restrict K).deg := by
  let w' : Place k (IntermediateField.adjoin K (C : Set Ω)) := w
  let _ : Algebra C (IntermediateField.adjoin K (C : Set Ω)) := constantAlgebra (K := K) C
  have : IsScalarTower k C (IntermediateField.adjoin K (C : Set Ω)) :=
    constantScalarTower (K := K) C
  have : IsScalarTower k K (IntermediateField.adjoin K (C : Set Ω)) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      Subtype.ext (IsScalarTower.algebraMap_apply k K Ω x)
  have : FiniteDimensional K (IntermediateField.adjoin K (C : Set Ω)) :=
    finiteDimensional_constantExtension_of_finite (K := K) C
  have : IsGalois K (IntermediateField.adjoin K (C : Set Ω)) :=
    isGalois_constantExtension (K := K) C
  have h := Place.deg_forgetConstants_eq_lcm
    (k := k) (C := C) (K := K) (E := IntermediateField.adjoin K (C : Set Ω))
    (constantExtension_adjoin_constants (K := K) C) (w'.extendConstants C)
  have hw : (w'.extendConstants C).forgetConstants (K := k) = w' := Place.ext rfl
  rw [hw] at h
  exact h

/-- The inertia degree in the actual constant compositum. -/
theorem inertiaDeg_constantExtension (w : Place k (constantExtensionStage (K := K) C)) :
    w.inertiaDeg K = Module.finrank k C / Nat.gcd (Module.finrank k C) (w.restrict K).deg := by
  let w' : Place k (IntermediateField.adjoin K (C : Set Ω)) := w
  let _ : Algebra C (IntermediateField.adjoin K (C : Set Ω)) := constantAlgebra (K := K) C
  have : IsScalarTower k C (IntermediateField.adjoin K (C : Set Ω)) :=
    constantScalarTower (K := K) C
  have : IsScalarTower k K (IntermediateField.adjoin K (C : Set Ω)) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      Subtype.ext (IsScalarTower.algebraMap_apply k K Ω x)
  have : FiniteDimensional K (IntermediateField.adjoin K (C : Set Ω)) :=
    finiteDimensional_constantExtension_of_finite (K := K) C
  have : IsGalois K (IntermediateField.adjoin K (C : Set Ω)) :=
    isGalois_constantExtension (K := K) C
  have h := Place.inertiaDeg_forgetConstants_eq_div_gcd
    (k := k) (C := C) (K := K) (E := IntermediateField.adjoin K (C : Set Ω))
    (constantExtension_adjoin_constants (K := K) C) (w'.extendConstants C)
  have hw : (w'.extendConstants C).forgetConstants (K := k) = w' := Place.ext rfl
  rw [hw] at h
  exact h

end FunctionField

namespace FunctionField

open AlgebraicCurve

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [IsSepClosed Ω]

/-- The residue extension degree over the full constants in the actual degree-`n` tower. -/
theorem inertiaDeg_fullConstantDegreeStage (n : ℕ) [NeZero n]
    (w : Place (algebraicClosure k K) (fullConstantDegreeStage k K Ω n)) :
    w.inertiaDeg K = n / Nat.gcd n (w.restrict K).deg := by
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  have : IsCurveOver (algebraicClosure k K) K := isCurveOver_fullConstants k K
  have h := inertiaDeg_constantExtension (K := K)
    (finiteConstantsInClosure (algebraicClosure k K) Ω n).toIntermediateField w
  rw [finrank_finiteConstantsInClosure] at h
  exact h

/-- A degree-`d` place over the full constants splits into `gcd(n,d)` places
in the actual degree-`n` constant extension. -/
theorem card_fiberOver_fullConstantDegreeStage (n : ℕ) [NeZero n]
    (w : Place (algebraicClosure k K) (fullConstantDegreeStage k K Ω n)) :
    ((w.restrict K).fiberOver (fullConstantDegreeStage k K Ω n)).card =
      Nat.gcd n (w.restrict K).deg := by
  have : Algebra.EssFiniteType k K := essFiniteType k K
  have : Finite (algebraicClosure k K) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k K
  have he : w.ramificationIndex K = 1 := ramificationIndex_constantExtension (K := K)
    (finiteConstantsInClosure (algebraicClosure k K) Ω n).toIntermediateField w
  have hc := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg
    (w.restrict K) w rfl
  rw [he, one_mul, finrank_fullConstantDegreeStage] at hc
  have hg : Nat.gcd n (w.restrict K).deg * w.inertiaDeg K = n := by
    rw [inertiaDeg_fullConstantDegreeStage k K Ω n w]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left n (w.restrict K).deg)
  exact mul_right_cancel₀ (Nat.ne_of_gt (w.inertiaDeg_pos (F := K))) (hc.trans hg.symm)

end FunctionField

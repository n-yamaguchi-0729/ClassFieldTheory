/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.FiniteExtensionFixed
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChange
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.AlgEquiv

/-!
# Rational degree on the actual idele-class direct limit

At a finite stage, divide the idele-class degree by the extension degree.
The actual inclusion degree formula makes these maps compatible, hence
defines a Galois-invariant homomorphism on the existing direct limit.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup.FiniteExtensionLimit

open FiniteExtensionSystem

variable {k K Ω : Type} [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [FunctionField k K]
    [Algebra K Ω] [Algebra k Ω] [Algebra (RatFunc k) Ω]
    [IsScalarTower k K Ω] [IsScalarTower (RatFunc k) K Ω]
    [IsScalarTower k (RatFunc k) Ω]

/-- Degree at a finite stage divided by its degree over the distinguished base. -/
def stageRationalDegree (E : FiniteGaloisIntermediateField K Ω) :
    stage (k := k) E →* Multiplicative ℚ where
  toFun c := Multiplicative.ofAdd
    ((degree (k := k) (K := E) c).toAdd / (Module.finrank K E : ℚ))
  map_one' := by
    apply Multiplicative.toAdd.injective
    change ((degree (k := k) (K := E) 1).toAdd : ℚ) / (Module.finrank K E : ℚ) = 0
    rw [map_one]
    exact zero_div _
  map_mul' c d := by
    apply Multiplicative.toAdd.injective
    change ((degree (k := k) (K := E) (c * d)).toAdd : ℚ) / (Module.finrank K E : ℚ) =
      ((degree (k := k) (K := E) c).toAdd : ℚ) / (Module.finrank K E : ℚ) +
        ((degree (k := k) (K := E) d).toAdd : ℚ) / (Module.finrank K E : ℚ)
    rw [map_mul, toAdd_mul, Int.cast_add, add_div]

/-- The actual degree formula makes the rational degree compatible with every stage inclusion. -/
theorem stageRationalDegree_transition (E F : FiniteGaloisIntermediateField K Ω)
    (h : E ≤ F) (c : stage (k := k) E) :
    stageRationalDegree F (transition (k := k) E F h c) = stageRationalDegree E c := by
  let aEF : Algebra E F := inclusionAlgebra h
  have hKEF : IsScalarTower K E F := inclusion_baseScalarTower h
  have hkEF : IsScalarTower k E F := inclusion_scalarTower h
  have hEFfin : FiniteDimensional E F := inclusion_finiteDimensional h
  have hEFgal : IsGalois E F := inclusion_isGalois h
  have hd : ((degree (k := k) (K := F) (transition (k := k) E F h c)).toAdd : ℚ) =
      (Module.finrank E F : ℚ) * (degree (k := k) (K := E) c).toAdd := by
    exact_mod_cast (degree_baseChange (k := k) (K := E) (L := F) c)
  have hn : (Module.finrank K F : ℚ) =
      (Module.finrank K E : ℚ) * (Module.finrank E F : ℚ) := by
    exact_mod_cast (Module.finrank_mul_finrank K E F).symm
  apply Multiplicative.toAdd.injective
  change ((degree (k := k) (K := F) (transition (k := k) E F h c)).toAdd : ℚ) /
      (Module.finrank K F : ℚ) =
    ((degree (k := k) (K := E) c).toAdd : ℚ) / (Module.finrank K E : ℚ)
  rw [hd, hn, mul_comm (Module.finrank E F : ℚ)]
  exact mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr (Module.finrank_pos (R := E) (M := F)).ne')

/-- The compatible rational degrees define a homomorphism on actual limit classes. -/
def rationalDegree : Limit k K Ω →* Multiplicative ℚ :=
  lift (k := k) (K := K) (Ω := Ω) (fun E => stageRationalDegree E)
    stageRationalDegree_transition

/-- Evaluation on the original finite-stage representative. -/
theorem rationalDegree_of (E : FiniteGaloisIntermediateField K Ω) (c : stage (k := k) E) :
    rationalDegree (k := k) (K := K) (Ω := Ω) (of (k := k) E c) = stageRationalDegree E c :=
  rfl

/-- Ambient Galois automorphisms preserve the actual rational degree. -/
theorem rationalDegree_smul (σ : Gal(Ω/K)) (c : Limit k K Ω) :
    rationalDegree (k := k) (K := K) (Ω := Ω) (σ • c) =
      rationalDegree (k := k) (K := K) (Ω := Ω) c := by
  obtain ⟨E, a, rfl⟩ := exists_of c
  rw [smul_of, rationalDegree_of, rationalDegree_of]
  apply Multiplicative.toAdd.injective
  change ((degree (k := k) (K := E) ((AlgEquiv.restrictNormalHom E σ) • a)).toAdd : ℚ) /
      (Module.finrank K E : ℚ) =
    ((degree (k := k) (K := E) a).toAdd : ℚ) / (Module.finrank K E : ℚ)
  exact congrArg (fun z : Multiplicative ℤ => (z.toAdd : ℚ) / (Module.finrank K E : ℚ))
    (degree_smul (AlgebraicCurve.SemilinearAut.ofAlgAut
      ((AlgEquiv.restrictNormalHom E σ).restrictScalars k)) a)

end FunctionField.IdeleClassGroup.FiniteExtensionLimit

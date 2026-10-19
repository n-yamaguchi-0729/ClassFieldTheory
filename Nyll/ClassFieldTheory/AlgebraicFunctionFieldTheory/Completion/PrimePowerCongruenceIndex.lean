/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.NormOpen
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.Basic
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrimePowerCongruenceIndex
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
import Mathlib.FieldTheory.Finiteness

/-!
# Prime-power congruence indices at actual places

The completion residue comparison and the residue degree turn the intrinsic
local index into the base-constant-field cardinality needed by Riemann–Roch.
-/

noncomputable section
open AlgebraicCurve
open scoped AlgebraicCurve.Place ValuativeRel

namespace FunctionField

variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- The actual local p-power congruence quotient has the cardinality
predicted by the place degree. -/
theorem card_completionPrimePowerCongruenceQuotient
    (p : ℕ) [Fact p.Prime] [CharP K p] (v : Place k K)
    (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (v.adicCompletionˣ ⧸
      ((powMonoidHom (α := v.adicCompletionˣ) p).range ⊔
        RayClass.localHigherUnitGroup v (p * n))) =
      p * Nat.card k ^ ((p * n - n) * v.deg) := by
  have hcurve : IsCurveOver k K := isCurveOver k K
  let relation : ValuativeRel v.adicCompletion := placeCompletionValuativeRel v
  have hlocal : IsNonarchimedeanLocalField v.adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField v
  have hchar : CharP v.adicCompletion p :=
    (Algebra.charP_iff K v.adicCompletion p).mp inferInstance
  let eO : 𝒪[v.adicCompletion] ≃+* v.adicCompletionIntegers :=
    RingEquiv.subringCongr (IdeleGroup.completionInteger_eq v)
  let e0 : v.ResidueField ≃+* IsLocalRing.ResidueField v.adicCompletionIntegers :=
    IsDedekindDomain.HeightOneSpectrum.ResidueFieldEquivCompletionResidueField
      K v.heightOneSpectrum
  let e : v.ResidueField ≃+* 𝓀[v.adicCompletion] :=
    e0.trans (IsLocalRing.ResidueField.mapEquiv eO.symm)
  have hres : Nat.card 𝓀[v.adicCompletion] = Nat.card k ^ v.deg := by
    have hfd : Module.Finite k v.ResidueField := IsCurveOver.finiteResidue v
    exact (Nat.card_congr e.symm.toEquiv).trans
      (Module.natCard_eq_pow_finrank (K := k) (V := v.ResidueField))
  have hc := LocalFieldTheory.card_primePowerCongruenceQuotient v.adicCompletion p n hn
  rw [hres, ← pow_mul, Nat.mul_comm v.deg (p * n - n)] at hc
  rw [sup_comm]
  exact hc

end FunctionField

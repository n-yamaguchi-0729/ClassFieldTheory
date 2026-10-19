/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.ConstantExtension.PicardNorm
import Nyll.AlgebraicCurves.Geometry.Picard.FiniteField.FiniteFieldPicardQuotient

/-!
# The actual Picard norm quotient for finite constant extensions

Transport the proved geometric norm quotient through the actual arithmetic
Picard comparisons, using the proved equality of actual and periodic norms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicCurve.CurveModel

attribute [local instance] SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup

variable {k Ω F₀ F : Type} [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    [Field F₀] [Algebra k F₀] [IsCurveOver k F₀] [Algebra.EssFiniteType k F₀]
    [Field F] [Algebra Ω F] [IsCurveOver Ω F]
    (M₀ : CurveModel k F₀) [GeometricallyIntegral M₀.toBase] (M : CurveModel Ω F)
    (e : M.C ≅ pullback M₀.toBase (specMap k Ω))
    (he : e.hom ≫ pullback.snd M₀.toBase (specMap k Ω) = M.toBase)
    (E : Type) [Field E] [Fintype E] [Algebra k E] [Algebra E Ω]
    [IsScalarTower k E Ω] [Algebra.IsAlgebraic E Ω]

local notation "CE" => pullback M₀.toBase (specMap k E)
local notation "cE" => pullback.snd M₀.toBase (specMap k E)
local notation "φ" => M.constantSemilinearAction M₀.toBase e he
  (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)
local notation "σ" => SemilinearAut.toRingAut φ
local notation "d" => Module.finrank k E

/-- The actual arithmetic norm corresponds to the geometric periodic norm. -/
theorem constantPicardNorm_periodic :
    let _ : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
    ∀ x : Pic E (CE).functionField,
      M₀.constantPicardFixedEquiv M e he (M₀.constantsAreBase_of_constantModel M e he)
          (M₀.constantPicardNorm M e he E x) =
        CyclicAction.periodicNorm φ d (M₀.constantPicardPeriodicEquiv M e he E x) := by
  intro algE x
  apply Subtype.ext
  exact M₀.constantPicardBaseChange_norm M e he E x

/-- The norm quotient of the actual arithmetic Picard groups is cyclic of the extension degree. -/
def constantPicardNormQuotientEquiv :
    let _ : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
    (Pic k F₀ ⧸ (M₀.constantPicardNorm M e he E).range) ≃+ ZMod d := by
  intro algE
  let b := M₀.constantPicardFixedEquiv M e he (M₀.constantsAreBase_of_constantModel M e he)
  let a := M₀.constantPicardPeriodicEquiv M e he E
  have hr : (M₀.constantPicardNorm M e he E).range.map b.toAddMonoidHom =
      (CyclicAction.periodicNorm (A := Pic Ω F) φ d).range := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      exact ⟨a x, (M₀.constantPicardNorm_periodic M e he E x).symm⟩
    · rintro ⟨x, rfl⟩
      refine ⟨M₀.constantPicardNorm M e he E (a.symm x), ⟨a.symm x, rfl⟩, ?_⟩
      change b (M₀.constantPicardNorm M e he E (a.symm x)) = _
      rw [constantPicardNorm_periodic]
      exact congrArg (CyclicAction.periodicNorm φ d) (a.apply_symm_apply x)
  exact (QuotientAddGroup.congr _ _ b hr).trans
    (JacobianVarieties.Picard.constantFrobenius_picardNormQuotientEquiv M₀.toBase M e he d
      (Module.finrank_pos (R := k) (M := E)).ne')

/-- The actual Picard norm index is the degree of the finite constant extension. -/
theorem natCard_constantPicardNormQuotient :
    let _ : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
    Nat.card (Pic k F₀ ⧸ (M₀.constantPicardNorm M e he E).range) = d := by
  intro algE
  have hn : NeZero d := ⟨(Module.finrank_pos (R := k) (M := E)).ne'⟩
  rw [Nat.card_congr (M₀.constantPicardNormQuotientEquiv M e he E).toEquiv,
    Nat.card_eq_fintype_card, ZMod.card]

/-- Degree divisibility exactly characterizes actual arithmetic Picard norms. -/
theorem mem_constantPicardNorm_range_iff (x : Pic k F₀) :
    let _ : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
    x ∈ (M₀.constantPicardNorm M e he E).range ↔
      (d : ℤ) ∣ H1Gm.degree k F₀ x := by
  intro algE
  have hC := M₀.constantsAreBase_of_constantModel M e he
  let b := M₀.constantPicardFixedEquiv M e he hC
  let a := M₀.constantPicardPeriodicEquiv M e he E
  have hxpow : φ ^ 1 • (b x : Pic Ω F) = b x := (b x).property
  have hx : φ • (b x : Pic Ω F) = b x := by simpa only [pow_one] using hxpow
  have hnorm := JacobianVarieties.Picard.exists_constantFrobenius_periodic_picard_norm_iff
    M₀.toBase M e he d (Module.finrank_pos (R := k) (M := E)).ne' (b x) hx
  have hdeg : H1Gm.degree Ω F (b x : Pic Ω F) = H1Gm.degree k F₀ x :=
    M₀.degree_constantPicardBaseChange M e he hC x
  rw [hdeg] at hnorm
  constructor
  · rintro ⟨y, rfl⟩
    apply hnorm.mp
    refine ⟨a y, (a y).property, ?_⟩
    exact (M₀.constantPicardBaseChange_norm M e he E y).symm
  · intro hdiv
    obtain ⟨y, hy, hsum⟩ := hnorm.mpr hdiv
    refine ⟨a.symm ⟨y, hy⟩, ?_⟩
    apply b.injective
    rw [constantPicardNorm_periodic]
    change CyclicAction.periodicNorm φ d (a (a.symm ⟨y, hy⟩)) = b x
    rw [AddEquiv.apply_symm_apply]
    exact Subtype.ext hsum

end AlgebraicCurve.CurveModel

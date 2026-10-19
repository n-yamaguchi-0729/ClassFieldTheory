/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.ConstantExtension.FunctionDescent
import Nyll.GaloisCohomology.FieldTheory.PeriodicGalois

/-!
# Actual finite Galois extensions from geometric Frobenius periods

The original function field is the fixed field proved by divisor descent.
Its canonical embedding into the period-n field gives a finite Galois
extension of degree n, using the exact order detected on finite constants.
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
    (M₀ : CurveModel k F₀) (M : CurveModel Ω F)
    (e : M.C ≅ pullback M₀.toBase (specMap k Ω))
    (he : e.hom ≫ pullback.snd M₀.toBase (specMap k Ω) = M.toBase)

local notation "φ" => M.constantSemilinearAction M₀.toBase e he
  (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)
local notation "σ" => SemilinearAut.toRingAut φ

/-- The actual original-field embedding into the geometric period-n field. -/
abbrev constantPeriodicAlgebra (hC : ConstantsAreBase k F₀) (n : ℕ) :
    Algebra F₀ (RingAut.periodicSubfield σ n) :=
  RingAut.periodicExtensionAlgebra σ n (M₀.constantFrobeniusFixedFieldEquiv M e he hC)

/-- Positive Frobenius periods give genuine degree-n finite Galois extensions of the base field. -/
theorem constantPeriodicExtension_properties (hC : ConstantsAreBase k F₀)
    (n : ℕ) (hn : n ≠ 0) :
    let _ := M₀.constantPeriodicAlgebra M e he hC n
    FiniteDimensional F₀ (RingAut.periodicSubfield σ n) ∧
      IsGalois F₀ (RingAut.periodicSubfield σ n) ∧
      Module.finrank F₀ (RingAut.periodicSubfield σ n) = n := by
  intro alg
  obtain ⟨hfin, hgal, hrank⟩ := RingAut.periodicExtension_properties σ n hn
    (M₀.constantFrobeniusFixedFieldEquiv M e he hC)
  refine ⟨hfin, hgal, hrank.trans ?_⟩
  exact FiniteField.orderOf_periodicAut_of_frobenius σ (fun a => by
    rw [← SemilinearAut.smul_def, SemilinearAut.smul_algebraMap,
      M.constantSemilinearAction_baseAut]
    rfl) n hn

end AlgebraicCurve.CurveModel

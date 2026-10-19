/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.ConstantExtension.PeriodicExtension
import Nyll.AlgebraicCurves.Models.ConstantExtension.BaseTower
import Nyll.AlgebraicCurves.Models.ConstantExtension.ModelConstants
import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField

/-!
# The actual finite base change and its Frobenius-periodic function field

Identify the function field of the finite base-changed curve with the appropriate
periodic subfield of the geometric function field. The actual curve projection
then gives a finite Galois extension of the original function field, of precisely
the constant-field degree.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicCurve.CurveModel

variable {k Ω F₀ F : Type} [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    [Field F₀] [Algebra k F₀] [Field F] [Algebra Ω F] [IsCurveOver Ω F]
    (M₀ : CurveModel k F₀) [GeometricallyIntegral M₀.toBase] (M : CurveModel Ω F)
    (e : M.C ≅ pullback M₀.toBase (specMap k Ω))
    (he : e.hom ≫ pullback.snd M₀.toBase (specMap k Ω) = M.toBase)
    (E : Type) [Field E] [Fintype E] [Algebra k E] [algEΩ : Algebra E Ω]
    [towerEΩ : IsScalarTower k E Ω] [hAlgEΩ : Algebra.IsAlgebraic E Ω]

local notation "CE" => pullback M₀.toBase (specMap k E)
local notation "cE" => pullback.snd M₀.toBase (specMap k E)
local notation "φ" => M.constantSemilinearAction M₀.toBase e he
  (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)
local notation "σ" => SemilinearAut.toRingAut φ

/-- The actual finite-base-change function field is the geometric Frobenius-periodic field. -/
def constantFunctionPeriodicEquiv :
    let _ : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
    (CE).functionField ≃+* RingAut.periodicSubfield σ (Module.finrank k E) := by
  intro alg
  have hcurve : IsCurveOver E (CE).functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one cE
      (RingEquiv.refl _) (fun _ => rfl)
  have hft : Algebra.EssFiniteType E (CE).functionField := essFiniteType_functionField cE
  let ME : CurveModel E (CE).functionField := ofSmoothProperCurve cE
  let eE := M.constantTowerModelIso k E Ω M₀.toBase e
  have heE := M.constantTowerModelIso_base k E Ω M₀.toBase e he
  have hC : ConstantsAreBase E (CE).functionField :=
    ME.constantsAreBase_of_constantModel M eE heE
  let ψ := M.constantSemilinearAction ME.toBase eE heE
    (FiniteField.frobeniusAlgEquivOfAlgebraic E Ω)
  have hψ : ψ = φ ^ Module.finrank k E :=
    M.constantSemilinearAction_frobenius_tower k E Ω M₀.toBase e he
  let ρ : SemilinearAut Ω F →* RingAut F :=
    (MonoidHom.fst (RingAut F) (RingAut Ω)).comp (SemilinearAut Ω F).subtype
  have hσ : SemilinearAut.toRingAut ψ = σ ^ Module.finrank k E := by
    rw [hψ]
    exact ρ.map_pow φ (Module.finrank k E)
  have hsub : RingAut.periodicSubfield (SemilinearAut.toRingAut ψ) 1 =
      RingAut.periodicSubfield σ (Module.finrank k E) := by
    rw [hσ]
    ext x
    change (((σ ^ Module.finrank k E) ^ 1) x = x) ↔ _
    rw [pow_one]
    rfl
  exact (ME.constantFrobeniusFixedFieldEquiv M eE heE hC).trans (RingEquiv.subfieldCongr hsub)

/-- The comparison uses the actual projection embedding into the geometric function field. -/
theorem constantFunctionPeriodicEquiv_apply (x : (CE).functionField) :
    let _ : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
    ((M₀.constantFunctionPeriodicEquiv M e he E x :
      RingAut.periodicSubfield σ (Module.finrank k E)) : F) =
      M.constantBaseEmbedding cE (M.constantTowerModelIso k E Ω M₀.toBase e) x := rfl

/-- The periodic-field comparison respects the actual original function-field embedding. -/
def constantFunctionPeriodicAlgEquiv [IsCurveOver k F₀] [Algebra.EssFiniteType k F₀] :
    let _ : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
    let _ : Algebra F₀ (CE).functionField :=
      M₀.constantModelAlgebra (ofSmoothProperCurve cE) (Iso.refl _)
    let _ : Algebra F₀ (RingAut.periodicSubfield σ (Module.finrank k E)) :=
      M₀.constantPeriodicAlgebra M e he (M₀.constantsAreBase_of_constantModel M e he)
        (Module.finrank k E)
    (CE).functionField ≃ₐ[F₀] RingAut.periodicSubfield σ (Module.finrank k E) := by
  intro algE alg₀ algP
  apply AlgEquiv.ofRingEquiv (f := M₀.constantFunctionPeriodicEquiv M e he E)
  intro x
  apply Subtype.ext
  rw [constantFunctionPeriodicEquiv_apply]
  exact M.constantBaseEmbedding_tower M₀.toBase e E (M₀.ffEquiv x)

omit [Fintype k] [Fintype E] in
include he algEΩ towerEΩ hAlgEΩ in
/-- The actual finite base change has the constant-field degree over the original function field. -/
theorem constantFiniteExtension_properties [Finite k] [Finite E]
    [IsCurveOver k F₀] [Algebra.EssFiniteType k F₀] :
    let _ : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
    let _ : Algebra F₀ (CE).functionField :=
      M₀.constantModelAlgebra (ofSmoothProperCurve cE) (Iso.refl _)
    FiniteDimensional F₀ (CE).functionField ∧ IsGalois F₀ (CE).functionField ∧
      Module.finrank F₀ (CE).functionField = Module.finrank k E := by
  intro algE alg₀
  let : Fintype k := Fintype.ofFinite k
  let : Fintype E := Fintype.ofFinite E
  have hC : ConstantsAreBase k F₀ := M₀.constantsAreBase_of_constantModel M e he
  let n := Module.finrank k E
  have hn : n ≠ 0 := (Module.finrank_pos (R := k) (M := E)).ne'
  let P := RingAut.periodicSubfield σ n
  let algP : Algebra F₀ P := M₀.constantPeriodicAlgebra M e he hC n
  obtain ⟨hfin, hgal, hrank⟩ := M₀.constantPeriodicExtension_properties M e he hC n hn
  let eqAlg := M₀.constantFunctionPeriodicAlgEquiv M e he E
  exact ⟨FiniteDimensional.of_injective eqAlg.toLinearMap eqAlg.injective,
    IsGalois.of_algEquiv eqAlg.symm, eqAlg.toLinearEquiv.finrank_eq.trans hrank⟩

end AlgebraicCurve.CurveModel

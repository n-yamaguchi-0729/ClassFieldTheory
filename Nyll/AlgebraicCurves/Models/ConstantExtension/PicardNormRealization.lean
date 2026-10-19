/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.ConstantExtension.PicardNormQuotient
import Nyll.AlgebraicCurves.Divisors.Norm.PicardNormCongr
import Nyll.GaloisCohomology.FieldTheory.ConstantTensorEquiv

/-!
# Picard norms for any actual realization of the constant compositum

The tensor multiplication maps compare the concrete curve base change with
a given constant-generated finite extension of the same degree. The proved
invariance of actual norms transports the norm criterion to that extension.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicCurve.CurveModel

attribute [local instance] SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup

variable {k Ω F₀ F : Type} [Field k] [Finite k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    [Field F₀] [Algebra k F₀] [IsCurveOver k F₀] [Algebra.EssFiniteType k F₀]
    [Field F] [Algebra Ω F] [IsCurveOver Ω F]
    (M₀ : CurveModel k F₀) [GeometricallyIntegral M₀.toBase] (M : CurveModel Ω F)
    (e : M.C ≅ pullback M₀.toBase (specMap k Ω))
    (he : e.hom ≫ pullback.snd M₀.toBase (specMap k Ω) = M.toBase)
    (E : Type) [Field E] [Finite E] [Algebra k E] [algEΩ : Algebra E Ω]
    [towerEΩ : IsScalarTower k E Ω] [hAlgEΩ : Algebra.IsAlgebraic E Ω]

local notation "CE" => pullback M₀.toBase (specMap k E)
local notation "cE" => pullback.snd M₀.toBase (specMap k E)
local notation "φ" => M.constantSemilinearAction M₀.toBase e he
  (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)
local notation "σ" => SemilinearAut.toRingAut φ
local notation "d" => Module.finrank k E

variable {L : Type} [Field L] [Algebra k L] [Algebra E L] [Algebra F₀ L]
    [IsScalarTower k E L] [IsScalarTower k F₀ L]
    [FiniteDimensional F₀ L] [IsGalois F₀ L] [HasPrincipalDivisors k L]

include he algEΩ towerEΩ hAlgEΩ in
/-- Any actual constant compositum of the expected degree has the proved Picard norm image. -/
theorem mem_picardNorm_range_iff_of_constantExtension
    (hgen : Algebra.adjoin F₀ (Set.range (algebraMap E L)) = ⊤)
    (hdeg : Module.finrank F₀ L = d) (x : Pic k F₀) :
    x ∈ (Pic.norm (k := k) (K := F₀) (L := L)).range ↔
      (d : ℤ) ∣ H1Gm.degree k F₀ x := by
  let fintypek : Fintype k := Fintype.ofFinite k
  let fintypeE : Fintype E := Fintype.ofFinite E
  let algE : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
  let ME : CurveModel E (CE).functionField := ofSmoothProperCurve cE
  let constAlg : Algebra k (CE).functionField :=
    ((algebraMap E (CE).functionField).comp (algebraMap k E)).toAlgebra
  have towerE : IsScalarTower k E (CE).functionField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let alg₀ : Algebra F₀ (CE).functionField := M₀.constantModelAlgebra ME (Iso.refl _)
  have tower₀ : IsScalarTower k F₀ (CE).functionField :=
    M₀.constantModel_isScalarTower ME (Iso.refl _) (Category.id_comp _)
  obtain ⟨hfin, hgal, -⟩ := M₀.constantFiniteExtension_properties M e he E
  have hcurve : IsCurveOver E (CE).functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one cE
      (RingEquiv.refl _) (fun _ => rfl)
  have hprincipal : HasPrincipalDivisors k (CE).functionField :=
    FunctionField.hasPrincipalDivisors_of_extendedConstants k E (CE).functionField
  have hgenCE : Algebra.adjoin F₀ (Set.range (algebraMap E (CE).functionField)) = ⊤ :=
    (M₀.constantModel_isIntegral_and_adjoin ME (Iso.refl _) (Category.id_comp _)).2
  have hdegCE : Module.finrank F₀ (CE).functionField = d :=
    (M₀.constantFiniteExtension_properties M e he E).2.2
  let eqCE := FieldTheory.constantTensorEquiv k E F₀ (CE).functionField hgenCE hdegCE
  let eqL := FieldTheory.constantTensorEquiv k E F₀ L hgen hdeg
  let eqFields : (CE).functionField ≃ₐ[F₀] L := eqCE.symm.trans eqL
  rw [Pic.range_norm_congrAlgEquiv eqFields, ← Pic.range_normConstants k E F₀ (CE).functionField]
  exact M₀.mem_constantPicardNorm_range_iff M e he E x

end AlgebraicCurve.CurveModel

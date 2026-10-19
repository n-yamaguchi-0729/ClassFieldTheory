/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.ConstantExtension.FunctionTower
import Nyll.GaloisCohomology.FieldTheory.PeriodicGaloisAction

/-!
# Frobenius on the actual finite constant base change

Transport the restricted geometric automorphism through the proved comparison
of actual function fields. It fixes the original function field, acts on the
geometric embedding by the original Frobenius, and generates the finite Galois group.
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

/-- The actual Frobenius automorphism over the original function field. -/
def constantFiniteFrobenius :
    let _ : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
    let _ : Algebra F₀ (CE).functionField :=
      M₀.constantModelAlgebra (ofSmoothProperCurve cE) (Iso.refl _)
    (CE).functionField ≃ₐ[F₀] (CE).functionField := by
  intro algE alg₀
  have hC := M₀.constantsAreBase_of_constantModel M e he
  let algP : Algebra F₀ (RingAut.periodicSubfield σ d) :=
    M₀.constantPeriodicAlgebra M e he hC d
  let eqP := M₀.constantFunctionPeriodicAlgEquiv M e he E
  exact AlgEquiv.autCongr eqP.symm (RingAut.periodicAlgAut σ d
    (M₀.constantFrobeniusFixedFieldEquiv M e he hC))

/-- The actual finite automorphism extends to the original geometric Frobenius. -/
theorem constantFiniteFrobenius_geometric (x : (CE).functionField) :
    let _ : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
    let _ : Algebra F₀ (CE).functionField :=
      M₀.constantModelAlgebra (ofSmoothProperCurve cE) (Iso.refl _)
    M.constantBaseEmbedding cE (M.constantTowerModelIso k E Ω M₀.toBase e)
        (M₀.constantFiniteFrobenius M e he E x) =
      φ • M.constantBaseEmbedding cE (M.constantTowerModelIso k E Ω M₀.toBase e) x := by
  intro algE alg₀
  let eqP := M₀.constantFunctionPeriodicEquiv M e he E
  have h : eqP (M₀.constantFiniteFrobenius M e he E x) = RingAut.periodicAut σ d (eqP x) := by
    change eqP (eqP.symm (RingAut.periodicAut σ d (eqP x))) = _
    exact eqP.apply_symm_apply _
  calc
    _ = (eqP (M₀.constantFiniteFrobenius M e he E x) : F) :=
      (M₀.constantFunctionPeriodicEquiv_apply M e he E _).symm
    _ = (RingAut.periodicAut σ d (eqP x) : F) := congrArg Subtype.val h
    _ = _ := by
      rw [SemilinearAut.smul_def]
      exact congrArg σ (M₀.constantFunctionPeriodicEquiv_apply M e he E x)

/-- The actual finite Frobenius has the full constant-extension degree as its exact order. -/
theorem orderOf_constantFiniteFrobenius :
    let _ : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
    let _ : Algebra F₀ (CE).functionField :=
      M₀.constantModelAlgebra (ofSmoothProperCurve cE) (Iso.refl _)
    orderOf (M₀.constantFiniteFrobenius M e he E) = d := by
  intro algE alg₀
  have hC := M₀.constantsAreBase_of_constantModel M e he
  let algP : Algebra F₀ (RingAut.periodicSubfield σ d) :=
    M₀.constantPeriodicAlgebra M e he hC d
  let eqP := M₀.constantFunctionPeriodicAlgEquiv M e he E
  change orderOf (AlgEquiv.autCongr eqP.symm (RingAut.periodicAlgAut σ d
    (M₀.constantFrobeniusFixedFieldEquiv M e he hC))) = d
  rw [MulEquiv.orderOf_eq, RingAut.orderOf_periodicAlgAut]
  exact FiniteField.orderOf_periodicAut_of_frobenius σ (fun a => by
    rw [← SemilinearAut.smul_def, SemilinearAut.smul_algebraMap,
      M.constantSemilinearAction_baseAut]
    rfl) d (Module.finrank_pos (R := k) (M := E)).ne'

/-- The actual finite Frobenius generates the entire actual Galois group. -/
theorem zpowers_constantFiniteFrobenius_eq_top :
    let _ : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
    let _ : Algebra F₀ (CE).functionField :=
      M₀.constantModelAlgebra (ofSmoothProperCurve cE) (Iso.refl _)
    Subgroup.zpowers (M₀.constantFiniteFrobenius M e he E) = ⊤ := by
  intro algE alg₀
  obtain ⟨hfin, hgal, hrank⟩ := M₀.constantFiniteExtension_properties M e he E
  apply (Subgroup.card_eq_iff_eq_top (Subgroup.zpowers (M₀.constantFiniteFrobenius M e he E))).mp
  rw [Nat.card_zpowers, M₀.orderOf_constantFiniteFrobenius M e he E,
    IsGalois.card_aut_eq_finrank, hrank]

/-- On the actual constant field the generator is the ordinary finite-field Frobenius. -/
theorem constantFiniteFrobenius_constants (a : E) :
    let _ : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
    let _ : Algebra F₀ (CE).functionField :=
      M₀.constantModelAlgebra (ofSmoothProperCurve cE) (Iso.refl _)
    M₀.constantFiniteFrobenius M e he E (algebraMap E (CE).functionField a) =
      algebraMap E (CE).functionField (FiniteField.frobeniusAlgEquivOfAlgebraic k E a) := by
  intro algE alg₀
  let eE := M.constantTowerModelIso k E Ω M₀.toBase e
  have heE := M.constantTowerModelIso_base k E Ω M₀.toBase e he
  let j := M.constantBaseEmbedding cE eE
  have hj (b : E) : j (algebraMap E (CE).functionField b) =
      algebraMap Ω F (algebraMap E Ω b) := M.constantBaseEmbedding_constants cE eE heE b
  apply j.injective
  rw [M₀.constantFiniteFrobenius_geometric M e he E, hj,
    SemilinearAut.smul_algebraMap, M.constantSemilinearAction_baseAut, hj]
  apply congrArg (algebraMap Ω F)
  change (algebraMap E Ω a) ^ Fintype.card k = algebraMap E Ω (a ^ Fintype.card k)
  exact (map_pow (algebraMap E Ω) a (Fintype.card k)).symm

/-- The same actual automorphism with its action on the extended constants recorded. -/
def constantFiniteSemilinearFrobenius :
    let _ : Algebra E (CE).functionField := (baseToFunctionField cE).toAlgebra
    SemilinearAut E (CE).functionField := by
  intro algE
  let alg₀ : Algebra F₀ (CE).functionField :=
    M₀.constantModelAlgebra (ofSmoothProperCurve cE) (Iso.refl _)
  exact ⟨((M₀.constantFiniteFrobenius M e he E).toRingEquiv,
    (FiniteField.frobeniusAlgEquivOfAlgebraic k E).toRingEquiv),
    M₀.constantFiniteFrobenius_constants M e he E⟩

end AlgebraicCurve.CurveModel

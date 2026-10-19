/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.ConstantExtension.SemilinearAction
import Nyll.SchemeTheory.Morphisms.FiniteFieldPointPeriod

/-!
# Frobenius periods of actual geometric places

The specified place corresponds to a geometric point of the curve model.
Its projection to the original curve has a finite field of definition, which
gives a positive period for the canonical semilinear action on the place.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra
open AlgebraicCurves.Models.Proofs
open CurveModel_exists_semilinearAut_baseAut_eq_and_pointEquivPlace_eq_smul
open AlgebraicCurve.CurveModel.GalPtSol

namespace AlgebraicCurve.CurveModel

variable {k Ω F : Type} [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω] [Field F] [Algebra Ω F]
    (M : CurveModel Ω F) {C : Scheme} (c : C ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType c] [IsSeparated c]
    (e : M.C ≅ pullback c (specMap k Ω))
    (he : e.hom ≫ pullback.snd c (specMap k Ω) = M.toBase)

/-- Each actual geometric place has a positive period under constant-field Frobenius. -/
theorem exists_constantFrobenius_place_period (w : Place Ω F) :
    ∃ n : ℕ, n ≠ 0 ∧
      (M.constantSemilinearAction c e he (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)) ^ n •
        w = w := by
  obtain ⟨p, rfl⟩ := M.pointEquivPlace.surjective w
  let q := p.1 ≫ e.hom ≫ pullback.fst c (specMap k Ω)
  have hq : q ≫ c = specMap k Ω := by
    change (p.1 ≫ e.hom ≫ pullback.fst c (specMap k Ω)) ≫ c = specMap k Ω
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.hom,
      he, ← Category.assoc, p.property, Category.id_comp]
  obtain ⟨n, hn, hp⟩ := exists_frobenius_period_of_algebraic_point k Ω c q hq
  let τ := (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) ^ n
  have hpoint : p.1 ≫ (M.coefficientIso c e τ).hom =
      Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ p.1 := by
    apply (cancel_mono e.hom).mp
    apply pullback.hom_ext
    · simp only [Category.assoc, coefficientIso_fst]
      exact hp.symm
    · simp only [Category.assoc, he, M.coefficientIso_base c e he τ]
      rw [← Category.assoc, p.property, Category.id_comp, Category.comp_id]
  have hw := point_clause M (M.coefficientIso c e τ) τ.toRingEquiv
    (M.coefficientIso_base c e he τ) p p hpoint
  refine ⟨n, hn, ?_⟩
  rw [← map_pow]
  exact hw.symm

end AlgebraicCurve.CurveModel

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

The imported formal section-to-place argument adapts the Anthropic FLT proof:
Copyright 2026 Anthropic, PBC. Released under Apache 2.0.
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_isRational_pointEquivPlace.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/

module

public import Nyll.AlgebraicCurves.Models.Ramification.Ramification
public import Nyll.AlgebraicCurves.Models.Sections.RationalSectionBoundaryPlace
public import Nyll.AlgebraicCurves.Places.Ramification.LocalUnramifiedRamification
public import Nyll.AlgebraicCurves.Places.ValuationRings.IsRationalRangeStalkSectionEq
public import Nyll.AlgebraicCurves.Places.Rational.Basic
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality
public import Nyll.SchemeTheory.FunctionFields.StalkFunctoriality
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Geometry

/-!
# Finite étale curve maps and the original closed-point places

The map on function fields is identified by the actual generic-point square.
The existing local unramified criterion then applies to the actual stalk map
at every closed point. Neither algebraic closedness nor a choice of rational
points representing all places is required.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicCurve.CurveModel

universe u v w

variable {k : Type u} [Field k]
variable {F : Type v} {E : Type w} [Field F] [Field E]
variable [Algebra k F] [Algebra k E]

/-- A finite étale map of the actual smooth proper curve models induces
the original place restriction and has ramification index one at every
closed point. The field embedding is identified by its generic square. -/
theorem closedPoint_restrictAlong_ramificationIndex_eq_one_of_finiteEtale
    (M : CurveModel k F) (N : CurveModel k E)
    (φ : F →ₐ[k] E) (hφ : φ.toRingHom.IsIntegral)
    (π : N.C ⟶ M.C) [IsFinite π] [Etale π]
    (hgeneric : N.C.fromSpecStalk (genericPoint N.C) ≫ π =
      Spec.map (CommRingCat.ofHom
        (N.ffEquiv.toRingHom.comp (φ.toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
          M.C.fromSpecStalk (genericPoint M.C))
    (y : closedPoints N.C) :
    ∃ hx : IsClosed ({π y.1} : Set M.C),
      (N.placeOfPoint y).restrictAlong φ hφ = M.placeOfPoint ⟨π y.1, hx⟩ ∧
        Place.ramificationIndexAlong φ (N.placeOfPoint y) = 1 := by
  have : IsFiniteEtale π := ⟨⟩
  have : Surjective π := IsFiniteEtale.surjective π
  let hdense : DenseRange π := π.surjective.denseRange
  have hfield : π.functionFieldMap hdense =
      N.ffEquiv.toRingHom.comp (φ.toRingHom.comp M.ffEquiv.symm.toRingHom) := by
    have hcat : CommRingCat.ofHom (π.functionFieldMap hdense) =
        CommRingCat.ofHom
          (N.ffEquiv.toRingHom.comp (φ.toRingHom.comp M.ffEquiv.symm.toRingHom)) := by
      apply Spec.map_injective
      apply (cancel_mono (M.C.fromSpecStalk (genericPoint M.C))).mp
      rw [EtaleFundamentalGroups.Spec_functionFieldMap_fromSpecStalk π hdense]
      exact hgeneric
    exact congrArg CommRingCat.Hom.hom hcat
  have hx : IsClosed ({π y.1} : Set M.C) := by
    simpa only [Set.image_singleton] using π.isClosedMap {y.1} y.2
  let x : closedPoints M.C := ⟨π y.1, hx⟩
  let eX := AlgebraicCurves.Models.Proofs.Ramification.HG1b.stalkEquivOfRange
    M x.1 (M.placeOfPoint x) (M.range_stalk_eq x)
  let eY := AlgebraicCurves.Models.Proofs.Ramification.HG1b.stalkEquivOfRange
    N y.1 (N.placeOfPoint y) (N.range_stalk_eq y)
  let : Algebra (M.C.presheaf.stalk x.1) (N.C.presheaf.stalk y.1) :=
    (π.stalkMap y.1).hom.toAlgebra
  have : IsLocalHom
      (algebraMap (M.C.presheaf.stalk x.1) (N.C.presheaf.stalk y.1)) :=
    inferInstanceAs (IsLocalHom (π.stalkMap y.1).hom)
  have : Algebra.EssFiniteType (M.C.presheaf.stalk x.1) (N.C.presheaf.stalk y.1) :=
    LocallyOfFiniteType.stalkMap π y.1
  have : Algebra.FormallyUnramified
      (M.C.presheaf.stalk x.1) (N.C.presheaf.stalk y.1) :=
    FormallyUnramified.stalkMap π y.1
  have hcompat : ∀ a : M.C.presheaf.stalk x.1,
      ((eY (algebraMap (M.C.presheaf.stalk x.1) (N.C.presheaf.stalk y.1) a) :
        (N.placeOfPoint y).toValuationSubring) : E) =
        φ ((eX a : (M.placeOfPoint x).toValuationSubring) : F) := by
    intro a
    change N.ffEquiv.symm
        (algebraMap (N.C.presheaf.stalk y.1) N.C.functionField (π.stalkMap y.1 a)) =
      φ (M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField a))
    rw [← π.functionFieldMap_algebraMap_stalk hdense y.1 a, hfield]
    exact N.ffEquiv.symm_apply_apply _
  exact ⟨hx,
    Place.restrictAlong_eq_of_local_map φ hφ (M.placeOfPoint x) (N.placeOfPoint y)
      eX eY hcompat,
    Place.ramificationIndexAlong_eq_one_of_local_map φ hφ
      (M.placeOfPoint x) (N.placeOfPoint y) eX eY hcompat⟩


end AlgebraicCurve.CurveModel

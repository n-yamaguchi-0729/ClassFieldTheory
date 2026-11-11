/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Charts.FiniteComplIsOpen
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.ReducedEtale
public import Nyll.SchemeTheory.Morphisms.FiniteEtaleGeometricallyReduced

/-! # The actual finite boundary of an open subscheme of a proper curve -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isProper CurveModel.isIntegral CurveModel.smooth

universe u v

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]

/-- The omitted places are exactly those whose actual closed points are
outside the image of the given open immersion. -/
def openBoundaryPlaces (M : CurveModel K F)
    {X : Scheme.{u}} (j : X ⟶ M.C) : Set (Place K F) :=
  {v | (M.placeEquiv.symm v).val ∉ Set.range j}

/-- Interior points avoid the actual boundary set. -/
theorem place_not_mem_openBoundaryPlaces
    (M : CurveModel K F) {X : Scheme.{u}} (j : X ⟶ M.C)
    (y : X) (x : closedPoints M.C) (hx : x.val = j y) :
    M.placeOfPoint x ∉ M.openBoundaryPlaces j := by
  change ¬ (M.placeEquiv.symm (M.placeOfPoint x)).val ∉ Set.range j
  rw [← M.placeEquiv_apply, M.placeEquiv.symm_apply_apply]
  exact fun h => h ⟨y, hx.symm⟩

/-- The geometric boundary is finite for a nonempty open curve. -/
theorem openBoundaryPlaces_finite
    (M : CurveModel K F) {X : Scheme.{u}} [Nonempty X]
    (j : X ⟶ M.C) [IsOpenImmersion j] :
    (M.openBoundaryPlaces j).Finite := by
  let V : M.C.Opens := ⟨Set.range j, j.isOpenEmbedding.isOpen_range⟩
  have hV : (V : Set M.C).Nonempty :=
    ⟨j (Classical.choice (inferInstance : Nonempty X)), Set.mem_range_self _⟩
  have hf := AlgebraicCurve.finite_compl_of_isOpen M.toBase V hV
  have hi : Function.Injective (fun v : Place K F => (M.placeEquiv.symm v).val) :=
    fun v w h => M.placeEquiv.symm.injective (Subtype.ext h)
  exact Set.Finite.preimage hi.injOn hf

/-- The reduced closed complement of the actual open curve. -/
def openBoundaryIdeal (M : CurveModel K F)
    {X : Scheme.{u}} (j : X ⟶ M.C) [IsOpenImmersion j] : M.C.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨(Set.range j)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩

/-- The canonical boundary inclusion has exactly the points omitted by the
original open immersion. -/
theorem range_openBoundaryIdeal_subschemeι
    (M : CurveModel K F) {X : Scheme.{u}}
    (j : X ⟶ M.C) [IsOpenImmersion j] :
    Set.range (M.openBoundaryIdeal j).subschemeι = (Set.range j)ᶜ := by
  rw [Scheme.IdealSheafData.range_subschemeι, openBoundaryIdeal,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- The canonical boundary has finitely many scheme points. -/
theorem finite_openBoundaryIdeal_subscheme
    (M : CurveModel K F) {X : Scheme.{u}} [Nonempty X]
    (j : X ⟶ M.C) [IsOpenImmersion j] :
    Finite (M.openBoundaryIdeal j).subscheme := by
  let V : M.C.Opens := ⟨Set.range j, j.isOpenEmbedding.isOpen_range⟩
  have hV : (V : Set M.C).Nonempty :=
    ⟨j (Classical.choice (inferInstance : Nonempty X)), Set.mem_range_self _⟩
  have hfinite : (Set.range (M.openBoundaryIdeal j).subschemeι).Finite := by
    rw [M.range_openBoundaryIdeal_subschemeι j]
    exact AlgebraicCurve.finite_compl_of_isOpen M.toBase V hV
  exact (Set.finite_range_iff (M.openBoundaryIdeal j).subschemeι.injective).mp hfinite

open AlgebraicCurves.Geometry.Schemes.Proofs.isReduced_of_etale.L3gen in
/-- The reduced boundary of a nonempty open of a proper smooth curve is a
finite étale scheme over the original perfect coefficient field. -/
theorem finite_etale_openBoundaryIdeal_toBase
    [PerfectField K] (M : CurveModel K F) {X : Scheme.{u}} [Nonempty X]
    (j : X ⟶ M.C) [IsOpenImmersion j] :
    IsFinite ((M.openBoundaryIdeal j).subschemeι ≫ M.toBase) ∧
      Etale ((M.openBoundaryIdeal j).subschemeι ≫ M.toBase) := by
  have : Finite (M.openBoundaryIdeal j).subscheme :=
    M.finite_openBoundaryIdeal_subscheme j
  have : LocallyQuasiFinite ((M.openBoundaryIdeal j).subschemeι ≫ M.toBase) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (fun _ => Set.toFinite _)
  have : IsFinite ((M.openBoundaryIdeal j).subschemeι ≫ M.toBase) :=
    IsFinite.of_locallyQuasiFinite _
  have : IsReduced (M.openBoundaryIdeal j).subscheme :=
    isReduced_subscheme_vanishingIdeal _
  exact ⟨inferInstance, etale_of_isFinite_of_isReduced_over_perfectField _⟩

/-- Every place outside the actual boundary is represented by a closed
point of the actual open curve. -/
theorem exists_closedPoint_of_not_mem_openBoundaryPlaces
    (M : CurveModel K F) {X : Scheme.{u}}
    (j : X ⟶ M.C) [IsOpenImmersion j]
    (v : Place K F) (hv : v ∉ M.openBoundaryPlaces j) :
    ∃ x : closedPoints X, j x.val = (M.placeEquiv.symm v).val := by
  classical
  have hmem : (M.placeEquiv.symm v).val ∈ Set.range j := not_not.mp hv
  obtain ⟨x, hx⟩ := hmem
  have hpre : j ⁻¹' ({(M.placeEquiv.symm v).val} : Set M.C) = {x} := by
    ext z
    change j z = (M.placeEquiv.symm v).val ↔ z = x
    rw [← hx]
    exact j.isOpenEmbedding.injective.eq_iff
  have hclosed : IsClosed ({x} : Set X) := by
    rw [← hpre]
    exact (M.placeEquiv.symm v).property.preimage j.continuous
  exact ⟨⟨x, hclosed⟩, hx⟩

end AlgebraicCurve.CurveModel
